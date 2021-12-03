/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.selects

import kotlin.contracts.*
import kotlin.coroutines.*

/**
 * Waits for the result of multiple suspending functions simultaneously like [select], but in an _unbiased_
 * way when multiple clauses are selectable at the same time.
 *
 * This unbiased implementation of `select` expression randomly shuffles the clauses before checking
 * if they are selectable, thus ensuring that there is no statistical bias to the selection of the first
 * clauses.
 *
 * See [select] function description for all the other details.
 */
public suspend inline fun <R> selectUnbiased(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    contract {
        callsInPlace(builder, InvocationKind.EXACTLY_ONCE)
    }
    return UnbiasedSelectImplementation<R>(coroutineContext).run {
        builder(this)
        doSelect()
    }
}

/**
 * The unbiased `select` inherits the [standard one][SelectImplementation],
 * but does not register clauses immediately. Instead, it stores all of them
 * in [clauses] lists, shuffles and registers them in the beginning of [doSelect]
 * (see [shuffleAndRegisterClauses]), and then delegates the rest
 * to the parent's [doSelect] implementation.
 */
@PublishedApi
internal open class UnbiasedSelectImplementation<R>(context: CoroutineContext) : SelectImplementation<R>(context) {
    private val clauses: MutableList<ClauseWithArguments> = arrayListOf()

    override fun SelectClause0.invoke(block: suspend () -> R) {
        clauses += ClauseWithArguments(this, null, block)
    }

    override fun <Q> SelectClause1<Q>.invoke(block: suspend (Q) -> R) {
        clauses += ClauseWithArguments(this, null, block)
    }

    override fun <P, Q> SelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) {
        clauses += ClauseWithArguments(this, param, block)
    }

    @PublishedApi
    override suspend fun doSelect(): R {
        shuffleAndRegisterClauses()
        return super.doSelect()
    }

    @Suppress("UNCHECKED_CAST")
    private fun shuffleAndRegisterClauses() = try {
        clauses.shuffle()
        clauses.forEach {
            when (val clause = it.clause) {
                is SelectClause0 -> {
                    clause.register(it.block as suspend () -> R)
                }
                is SelectClause1<*> -> {
                    clause.register(it.block as suspend (Any?) -> R)
                }
                is SelectClause2<*, *> -> {
                    clause as SelectClause2<Any?, suspend (Any?) -> R>
                    clause.register(it.param, it.block as suspend (Any?) -> R)
                }
            }
        }
    } finally {
        clauses.clear()
    }

    private class ClauseWithArguments(val clause: SelectClause, val param: Any?, val block: Any?)
}