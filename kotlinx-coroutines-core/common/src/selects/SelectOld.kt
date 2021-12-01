/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.ScopeCoroutine
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

internal suspend inline fun <R> selectOld(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val scope = SelectBuilderImpl(uCont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.getResult()
    }
}

@PublishedApi
internal class SelectBuilderImpl<R>(
    uCont: Continuation<R> // unintercepted delegate continuation
) : SelectImplementation<R>(uCont.context) {
    private val cont = getOrCreateCancellableContinuation(uCont.intercepted())

    @PublishedApi
    internal fun getResult(): Any? {
        CoroutineScope(context).launch(context, start = CoroutineStart.UNDISPATCHED) {
            val result = doSelect()
            cont.resume(result)
        }
        return cont.getResult()
    }

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) {
        cont.resumeWithException(e)
    }
}


//internal suspend inline fun <R> selectUnbiasedOld(crossinline builder: SelectBuilder<R>.() -> Unit): R =
//    suspendCoroutineUninterceptedOrReturn { uCont ->
//        val scope = UnbiasedSelectBuilderImpl(uCont)
//        try {
//            builder(scope)
//        } catch (e: Throwable) {
//            scope.handleBuilderException(e)
//        }
//        scope.initSelectResult()
//    }