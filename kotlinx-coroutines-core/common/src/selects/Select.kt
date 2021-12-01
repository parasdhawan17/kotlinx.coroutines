/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.sync.*
import kotlin.contracts.*
import kotlin.coroutines.*

/**
 * Waits for the result of multiple suspending functions simultaneously, which are specified using _clauses_
 * in the [builder] scope of this select invocation. The caller is suspended until one of the clauses
 * is either _selected_ or _fails_.
 *
 * At most one clause is *atomically* selected and its block is executed. The result of the selected clause
 * becomes the result of the select. If any clause _fails_, then the select invocation produces the
 * corresponding exception. No clause is selected in this case.
 *
 * This select function is _biased_ to the first clause. When multiple clauses can be selected at the same time,
 * the first one of them gets priority. Use [selectUnbiased] for an unbiased (randomized) selection among
 * the clauses.

 * There is no `default` clause for select expression. Instead, each selectable suspending function has the
 * corresponding non-suspending version that can be used with a regular `when` expression to select one
 * of the alternatives or to perform the default (`else`) action if none of them can be immediately selected.
 *
 * ### List of supported select methods
 *
 * | **Receiver**     | **Suspending function**                           | **Select clause**
 * | ---------------- | ---------------------------------------------     | -----------------------------------------------------
 * | [Job]            | [join][Job.join]                                  | [onJoin][Job.onJoin]
 * | [Deferred]       | [await][Deferred.await]                           | [onAwait][Deferred.onAwait]
 * | [SendChannel]    | [send][SendChannel.send]                          | [onSend][SendChannel.onSend]
 * | [ReceiveChannel] | [receive][ReceiveChannel.receive]                 | [onReceive][ReceiveChannel.onReceive]
 * | [ReceiveChannel] | [receiveCatching][ReceiveChannel.receiveCatching] | [onReceiveCatching][ReceiveChannel.onReceiveCatching]
 * | [Mutex]          | [lock][Mutex.lock]                                | [onLock][Mutex.onLock]
 * | none             | [delay]                                           | [onTimeout][SelectBuilder.onTimeout]
 *
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
 * function is suspended, this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 *
 * Note that this function does not check for cancellation when it is not suspended.
 * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
 */
public suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    contract {
        callsInPlace(builder, InvocationKind.EXACTLY_ONCE)
    }
    return SelectImplementation<R>(coroutineContext).run {
        builder(this)
        doSelect()
    }
}

/**
 * Scope for [select] invocation.
 */
public interface SelectBuilder<in R> {
    /**
     * Registers a clause in this [select] expression without additional parameters that does not select any value.
     */
    public operator fun SelectClause0.invoke(block: suspend () -> R)

    /**
     * Registers clause in this [select] expression without additional parameters that selects value of type [Q].
     */
    public operator fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R)

    /**
     * Registers clause in this [select] expression with additional parameter of type [P] that selects value of type [Q].
     */
    public operator fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R)

    /**
     * Registers clause in this [select] expression with additional nullable parameter of type [P]
     * with the `null` value for this parameter that selects value of type [Q].
     */
    public operator fun <P, Q> SelectClause2<P?, Q>.invoke(block: suspend (Q) -> R): Unit = invoke(null, block)

    /**
     * Clause that selects the given [block] after a specified timeout passes.
     * If timeout is negative or zero, [block] is selected immediately.
     *
     * **Note: This is an experimental api.** It may be replaced with light-weight timer/timeout channels in the future.
     *
     * @param timeMillis timeout time in milliseconds.
     */
    @ExperimentalCoroutinesApi
    @Deprecated(
        message = "Replaced with the same extension function",
        level = DeprecationLevel.HIDDEN, replaceWith = ReplaceWith("onTimeout")
    )
    public fun onTimeout(timeMillis: Long, block: suspend () -> R): Unit = onTimeout(timeMillis, block)
}

/**
 * Each [select] clause should be provided with:
 * 1) the [object of this clause][clauseObject],
 *    such as the channel instance for `onSend` and `onReceive`;
 * 2) the function that specifies how this clause
 *    should be registered in the object above ([regFunc]);
 * 3) the function that modifies the resumption result
 *    (passed via [SelectInstance.trySelect]) to the argument
 *    of the user-specified block.
 */
@InternalCoroutinesApi
public sealed interface SelectClause {
    public val clauseObject: Any
    public val regFunc: RegistrationFunction
    public val processResFunc: ProcessResultFunction
}

@InternalCoroutinesApi
public typealias RegistrationFunction = (clauseObject: Any, select: SelectInstance<*>, param: Any?) -> Unit
@InternalCoroutinesApi
public typealias ProcessResultFunction = (clauseObject: Any, param: Any?, clauseResult: Any?) -> Any?

/**
 * Clause for [select] expression without additional parameters that does not select any value.
 */
public interface SelectClause0 : SelectClause

@InternalCoroutinesApi
public class SelectClause0Impl(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction
) : SelectClause0 {
    override val processResFunc: ProcessResultFunction = DUMMY_PROCESS_RESULT_FUNCTION
}

private val DUMMY_PROCESS_RESULT_FUNCTION: ProcessResultFunction = { _, _, _ -> null }

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public interface SelectClause1<out Q> : SelectClause

@InternalCoroutinesApi
public class SelectClause1Impl<Q>(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : SelectClause1<Q>

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public interface SelectClause2<in P, out Q> : SelectClause

@InternalCoroutinesApi
public class SelectClause2Impl<P, Q>(
    override val clauseObject: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : SelectClause2<P, Q>

/**
 * Internal representation of select instance.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi // todo: sealed interface https://youtrack.jetbrains.com/issue/KT-22286
public interface SelectInstance<in R> {
    /**
     * This function should be called by other operations which are trying to perform a rendezvous with this `select`.
     * Returns `true` if the rendezvous succeeds, `false` otherwise.
     */
    public fun trySelect(clauseObject: Any, result: Any?): Boolean

    /**
     * This function should be called when this `select` is registered as a waiter. A function which removes the waiter
     * after this `select` is processed should be provided as a parameter.
     */
    public fun invokeOnCompletion(onCompleteAction: OnCompleteAction)

    /**
     * This function should be called during this `select` registration phase on a successful rendezvous.
     */
    public fun selectInRegPhase(selectResult: Any?)
}

@InternalCoroutinesApi
public typealias OnCompleteAction = () -> Unit

@PublishedApi
internal open class SelectImplementation<R> constructor(
    /**
     * The context of the coroutine that is performing this `select` operation.
     */
    val context: CoroutineContext
) : CancelHandler(), SelectBuilder<R>, SelectInstance<R> {

    /**
     * The `select` operation is split into three phases: registration, waiting, and clean-up.
     *
     * == Phase 1: Registration ==
     * In the first, registration phase, [SelectBuilder] is applied, and all the clauses register
     * via the provided [registration function][SelectClause.regFunc]. Intuitively, `select` registration
     * is similar to the plain blocking operation, with the only difference that this [SelectInstance]
     * is stored instead of continuation, and [SelectInstance.trySelect] is used to make a rendezvous.
     * Also, when registering, it is possible for the operation to complete immediately, without waiting.
     * In the latter case, [SelectInstance.selectInRegPhase] should be used. Otherwise, a cancellation
     * handler should be specified via [SelectInstance.invokeOnCompletion].
     *
     * After the [SelectBuilder] is processed, the registration completes s
     *
     *
     *
     */

    /**
     * List of clauses waiting on this `select` instance.
     */
    private val clauses = ArrayList<ClauseData<R>>(2)

    /**
     * The state of this `select` operation.
     */
    private val state = atomic<Any>(STATE_REG)
    /**
     * Returns `true` if this `select` operation is logically in REGISTRATION state;
     * otherwise, returns `false`.
     */
    private val inRegistrationState
        get() = state.value.let {
            it === STATE_REG || it is List<*>
        }

    /**
     * Stores the completion action provided through [invokeOnCompletion] during clause registration.
     * After that, if the clause is successfully registered (so, it has not completed immediately),
     * this [OnCompleteAction] is stored into the corresponding [ClauseData] instance.
     */
    private var onCompleteAction: OnCompleteAction? = null

    /**
     * Stores the result passed via [selectInRegPhase] during clause registration
     * or [trySelect], which is called by another coroutine trying to make a rendezvous
     * with this `select` instance. Further, this result is processed via the
     * [ProcessResultFunction] of the selected clause.
     *
     * Unfortunately, we cannot store the result in the [state] field, as the latter stores
     * the clause object (see [ClauseData.clauseObject] and [SelectClause.clauseObject]).
     * Instead, it is possible to merge the [result] and [onCompleteAction] fields into
     * one that stores either result, if the clause is registered ([inRegistrationState] is `true`),
     * or [OnCompleteAction] instance, if the clause is selected during registration ([inRegistrationState] is `false`).
     * Yet, this optimization is omitted for simplicity.
     */
    private var result: Any? = NO_RESULT

    @PublishedApi
    internal open suspend fun doSelect(): R = if (isSelected) complete() else doSelectSuspend()

    private suspend fun doSelectSuspend(): R {
        waitUntilSelected()
        return complete()
    }

    private val isSelected get() = state.value is ClauseData<*>

    private suspend fun complete(): R {
        val selectedClause = state.value as ClauseData<R>
        val result = selectedClause.processResult(result)
        cleanup(selectedClause)
        return selectedClause.invokeBlock(result)
    }

    /**
     * Return an index of the selected alternative in `alternatives` array.
     */
    private fun findClause(objForSelect: Any) =
        clauses.find { it.clauseObject === objForSelect } ?: error("Clause with object $objForSelect is not found")

    override fun SelectClause0.invoke(block: suspend () -> R) = register(block)
    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) = register(param, block)
    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) = register(block)

    protected fun SelectClause0.register(block: suspend () -> R) {
        val clause = ClauseData<R>(clauseObject, regFunc, processResFunc, PARAM_CLAUSE_0, block)
        registerClause(clause)
    }

    protected fun <Q> SelectClause1<Q>.register(block: suspend (Q) -> R) {
        val clause = ClauseData<R>(clauseObject, regFunc, processResFunc, PARAM_CLAUSE_1, block)
        registerClause(clause)
    }

    protected fun <P, Q> SelectClause2<P, Q>.register(param: P, block: suspend (Q) -> R) {
        val clause = ClauseData<R>(clauseObject, regFunc, processResFunc, param, block)
        registerClause(clause)
    }

    private fun registerClause(clause: ClauseData<R>) {
        if (state.value is ClauseData<*>) return
        checkClauseObject(clause.clauseObject)
        if (clause.tryRegister(this@SelectImplementation)) {
            clauses += clause
            clause.onCompleteAction = onCompleteAction
            onCompleteAction = null
        } else {
            state.value = clause
        }
    }

    private fun checkClauseObject(clauseObject: Any) {
        check(!clauses.any { it.clauseObject === clauseObject }) {
            "Cannot use select clauses on the same object: $clauseObject"
        }
    }

    override fun invokeOnCompletion(onCompleteAction: OnCompleteAction) {
        this.onCompleteAction = onCompleteAction
    }

    override fun selectInRegPhase(selectResult: Any?) {
        this.result = selectResult
    }

    private suspend fun waitUntilSelected() {
        // Slow path: suspend and wait until selected.
        return waitUntilSelectedSuspend()
    }

    private suspend fun waitUntilSelectedSuspend() = suspendCancellableCoroutineReusable<Unit> sc@ { cont ->
        cont.invokeOnCancellation(this.asHandler)
        state.loop { curState ->
            when {
                curState === STATE_REG -> if (state.compareAndSet(curState, cont)) return@sc
                curState is ClauseData<*> -> {
                    cont.resume(Unit)
                    return@sc
                }
                curState is List<*> -> {
                    curState as List<ClauseData<R>>
                    curState.forEach { registerClause(it) }
                }
                else -> error("unexpected state: $curState")
            }
        }
    }

    override fun trySelect(clauseObject: Any, result: Any?): Boolean {
        // Find the clause with the specified object.
        val clause = findClause(clauseObject)
        // Try to select this clause.
        val cont = trySelectClause(clause) ?: return false
        // Success!
        this.result = result
        return cont.tryResume().also { success ->
            if (!success) this.result = NO_RESULT
        }
    }

    private fun trySelectClause(clause: ClauseData<R>): CancellableContinuation<Unit>? = state.loop { curState ->
        when(curState) {
            // Perform a rendezvous with this select if it is in WAITING state.
            is CancellableContinuation<*> -> {
                if (state.compareAndSet(curState, clause)) return curState as CancellableContinuation<Unit>
            }
            // Already selected on the corresponding clause.
            is ClauseData<*> -> return null
            // Already selected and completed.
            STATE_COMPLETED -> return null
            // This select is still in REGISTRATION phase, re-register the clause
            // in order not to wait until this select moves to WAITING phase.
            // This is a rare race, so we do not need to worry about performance here.
            STATE_REG -> if (state.compareAndSet(curState, listOf(clause))) return null
            // This select is still in REGISTRATION phase, and the state stores a list of clauses
            // for re-registration, add the selecting clause to this list.
            // This is a rare race, so we do not need to worry about performance here.
            is List<*> -> if (state.compareAndSet(curState, curState + clause)) return null
            else -> error("Unexpected state: $curState")
        }
    }

    private fun cleanup(selectedClause: ClauseData<R>? = null) {
        // Invoke all cancellation handlers except for the
        // one related to the selected clause, if specified.
        clauses.forEach { clause ->
            if (clause !== selectedClause) clause.onCompleteAction?.invoke()
        }
        // Clear all the remaining data to avoid memory leaks.
        clauses.clear()
        result = null
        state.value = STATE_COMPLETED
    }

    // [CompletionHandler] implementation
    override fun invoke(cause: Throwable?) = cleanup()

    /**
     * Each `select` clause is internally represented with a [ClauseData] instance.
      */
    private class ClauseData<R>(
        val clauseObject: Any,
        val regFunc: RegistrationFunction,
        val processResFunc: ProcessResultFunction,
        val param: Any?,
        val block: Any,
        var onCompleteAction: OnCompleteAction? = null
    ) {
        fun tryRegister(select: SelectImplementation<R>): Boolean {
            // Invariant: the specified select is in REGISTRATION
            // state and
            assert { select.state.value === STATE_REG }
            assert { select.result === NO_RESULT }
            // Invoke the registration function.
            regFunc(clauseObject, select, param)
            // Check whether the
            return select.result === NO_RESULT
        }

        fun processResult(result: Any?) = try {
            processResFunc(clauseObject, param, result)
        } catch (e: Throwable) {
            throw recoverStackTrace(e)
        }

        suspend fun invokeBlock(result: Any?): R {
            val block = block
            return if (param === PARAM_CLAUSE_0) {
                block as suspend () -> R
                block()
            } else {
                block as suspend (Any?) -> R
                block(result)
            }
        }
    }
}

private fun CancellableContinuation<Unit>.tryResume(): Boolean {
    val token = tryResume(Unit) ?: return false
    completeResume(token)
    return true
}

// Markers for REGISTRATION and COMPLETED states.
private val STATE_REG = Symbol("STATE_REG")
private val STATE_COMPLETED = Symbol("STATE_COMPLETED")
// As the selection result is nullable, we use this special
// marker for the absence of result.
private val NO_RESULT = Symbol("NO_RESULT")
// We use this marker parameter objects to distinguish
// SelectClause[0,1,2] and invoke the `block` correctly.
private val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
private val PARAM_CLAUSE_1 = Symbol("PARAM_CLAUSE_1")