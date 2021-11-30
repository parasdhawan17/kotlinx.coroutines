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
    return SelectImplementation<R>().run {
        prepare()
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
internal open class SelectImplementation<R> : SelectBuilder<R>, SelectInstance<R> {
    //
    private val cont = atomic<Any?>(null)

    // The context of the coroutine that performs this `select`.
    private lateinit var _context: CoroutineContext
    val context: CoroutineContext get() = _context

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


    private val clauses = ArrayList<ClauseData<R>>(2)
    private val state = atomic<Any>(STATE_REG)

    private var onCompleteAction: (() -> Unit)? = null

    private var clauseResult: Any? = NO_RESULT

    suspend fun prepare() {
        // We need to save the coroutine context for the `onTimeout` operator.
        this._context = coroutineContext
    }

    open suspend fun doSelect(): R {
        // The clauses are already registered.
        // Yet, there can be clauses to re-register stored
        // in `state` field. Re-register them if required
        // and move the state to WAITING.
        if (reregisterAndMoveToWaiting()) {
            suspendUntilSelected()
        }
        val selectedClause = state.value as ClauseData<R>
        val result = selectedClause.processResult(clauseResult)
        cleanup(selectedClause)
        return selectedClause.invokeBlock(result)
    }

    private fun reregisterAndMoveToWaiting(): Boolean {
        state.loop { curState ->
            when {
                curState === STATE_REG -> if (state.compareAndSet(curState, STATE_WAITING)) return true
                curState is ClauseData<*> -> return false
                curState is List<*> -> {
                    curState as List<ClauseData<R>>
                    curState.forEach { registerClause(it) }
                }
                else -> error("unexpected state: $curState")
            }
        }
    }

    /**
     * Suspends until successful [tryResume] invocation is performed.
     */
    private suspend fun suspendUntilSelected() = suspendCancellableCoroutineReusable<Unit> { cont ->
        // Try to store the continuation into `cont` field if it is not CONT_RESUMED.
        // In the latter case, complete immediately.
        if (!this.cont.compareAndSet(null, cont)) cont.resume(Unit)
        // On cancellation, perform a cleanup to avoid memory leaks.
        cont.invokeOnCancellation { cleanup() }
    }

    /**
     * Resumes the suspended (or aimed at suspending) [doSelect] call.
     * See [suspendUntilSelected] that also manipulates [cont].
     */
    private fun tryResume(): Boolean {
        var cont = this.cont.value
        // Does `cont` field stores a coroutine?
        if (cont === null) {
            // The field is still empty. Try to put CONT_RESUMED to inform `suspendUntilSelected`
            // that it should not suspend, and complete immediately after that.
            if (this.cont.compareAndSet(null, CONT_RESUMED)) return true
            // The CONT_RESUMED installation has failed => a continuation is stored, read it.
            cont = this.cont.value!!
        }
        // Try to resume the continuation if it is not cancelled yet.
        // Return `true` on success and `false` otherwise.
        cont as CancellableContinuation<Unit>
        val resumeToken = cont.tryResume(Unit) ?: return false
        cont.completeResume(resumeToken)
        return true
    }

    /**
     * Return an index of the selected alternative in `alternatives` array.
     */
    private fun findClause(objForSelect: Any) =
        clauses.find { it.clauseObject === objForSelect } ?: error("Clause with object $objForSelect is not found")

    private fun moveStateToDone(objForSelect: Any) {
        // Replace the state with DONE.
        // It is possible that there were clauses
        // to re-register -- we simply ignore them.
        state.value = findClause(objForSelect)
    }

    // == Phase 1: Registration ==

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
        val registered = clause.register(this@SelectImplementation)
        if (registered) {
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
        this.clauseResult = selectResult
    }

    private fun cleanup(selectedClause: ClauseData<R>? = null) {
        // Invoke all cancellation handlers except for the
        // one related to the selected clause, if specified.
        clauses.forEach { clause ->
            if (clause !== selectedClause) clause.onCompleteAction?.invoke()
        }
        // Clear all the remaining data to avoid memory leaks.
        this.clauses.clear()
        this.cont.value = null
        this.clauseResult = null
    }

    override fun trySelect(clauseObject: Any, result: Any?): Boolean {
        // Find the clause with the specified object.
        val clause = findClause(clauseObject)
        // Try to select this clause.
        if (!trySelectClause(clause)) return false
        // Success!
        this.clauseResult = result
        return tryResume().also { success ->
            if (!success) this.clauseResult = NO_RESULT
        }
    }

    private fun trySelectClause(clause: ClauseData<R>): Boolean = state.loop { curState ->
        when {
            // Perform a rendezvous with this select if it is in WAITING state.
            curState === STATE_WAITING -> if (state.compareAndSet(curState, clause)) return true
            // Already selected on the corresponding clause.
            curState is ClauseData<*> -> return false
            // This select is still in REGISTRATION phase, re-register the clause
            // in order not to wait until this select moves to WAITING phase.
            // This is a rare race, so we do not need to worry about performance here.
            curState === STATE_REG -> if (state.compareAndSet(curState, listOf(clause))) return false
            // This select is still in REGISTRATION phase, and the state stores a list of clauses
            // for re-registration, add the selecting clause to this list.
            // This is a rare race, so we do not need to worry about performance here.
            curState is List<*> -> if (state.compareAndSet(curState, curState + clause)) return false
            // Already selected with `objForSelect == curState`.
            else -> error("Unexpected state: $curState")
        }
    }

    private class ClauseData<R>(
        val clauseObject: Any,
        val regFunc: RegistrationFunction,
        val processResFunc: ProcessResultFunction,
        val param: Any?,
        val block: Any,
        var onCompleteAction: OnCompleteAction? = null
    ) {
        fun register(select: SelectImplementation<R>): Boolean {
            assert { select.state.value === STATE_REG }
            assert { select.clauseResult === NO_RESULT }
            regFunc(clauseObject, select, param)
            return select.clauseResult === NO_RESULT
        }

        fun processResult(result: Any?) = recoverStacktraceIfNeeded {
            processResFunc(clauseObject, param, result)
        }

        suspend fun invokeBlock(result: Any?): R = recoverStacktraceIfNeeded {
            val block = block
            if (param === PARAM_CLAUSE_0) {
                block as suspend () -> R
                block()
            } else {
                block as suspend (Any?) -> R
                block(result)
            }
        }
    }
}

private inline fun <R> recoverStacktraceIfNeeded(block: () -> R): R = try {
    block()
} catch (e: Throwable) {
    throw recoverStackTrace(e)
}

private val STATE_REG = Symbol("REG")
private val STATE_WAITING = Symbol("WAITING")

private val CONT_RESUMED = Symbol("CONT_RESUMED")

private val NO_RESULT = Symbol("NO_RESULT")

private val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
private val PARAM_CLAUSE_1 = Symbol("PARAM_CLAUSE_1")