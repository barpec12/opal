/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.br.reader

import org.opalj.bi.TestResources.locateTestResources
import org.opalj.br.instructions.INVOKEDYNAMIC

/**
 * This test loads all classes found in the Scala 2.12.4 libraries and verifies that all
 * suported [[INVOKEDYNAMIC]] instructions can be resolved.
 *
 * @author Arne Lottmann
 * @author Andreas Amuttsch
 * @author Michael Eichberg
 */
class ScalaLambdaExpressionsRewritingTest extends LambdaExpressionsRewritingTest {

    test("rewriting of invokedynamic instructions in Scala 2.12.4 library") {
        val project = load(locateTestResources("classfiles/scala-2.12.4", "bi"))

        val invokedynamics = project.allMethodsWithBody.par.flatMap { method ⇒
            method.body.get.collect {
                case i: INVOKEDYNAMIC if (
                    LambdaExpressionsRewriting.isJava8LikeLambdaExpression(i) ||
                    LambdaExpressionsRewriting.isScalaLambdaDeserializeExpression(i) ||
                    LambdaExpressionsRewriting.isScalaSymbolExpression(i)
                ) ⇒ i
            }
        }

        if (invokedynamics.nonEmpty) {
            fail(invokedynamics.mkString("Could not resolve:", "\n", "\n"))
        }
    }
}
