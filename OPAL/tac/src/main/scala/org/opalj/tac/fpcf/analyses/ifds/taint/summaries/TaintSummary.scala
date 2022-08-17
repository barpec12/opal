/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.tac.fpcf.analyses.ifds.taint.summaries

import org.opalj.br.{ArrayType, BooleanType, ByteType, CharType, FieldType, IntegerType, ObjectType, ShortType, Type, VoidType}
import org.opalj.tac.Call
import org.opalj.tac.fpcf.analyses.ifds.JavaIFDSProblem.V
import org.opalj.tac.fpcf.analyses.ifds.{JavaIFDSProblem, JavaStatement}
import org.opalj.tac.fpcf.analyses.ifds.taint.{ArrayElement, InstanceField, TaintFact, TaintNullFact, Variable}
import org.opalj.tac.fpcf.analyses.ifds.taint.summaries.Flow.nodeToTaint
import org.opalj.tac.fpcf.analyses.ifds.taint.summaries.TaintSummary.{signaturePattern, stringToFieldType, stringToReturnType}

import scala.util.matching.Regex
import scala.xml.Node

/**
 * Class which holds the methods summaries for a single class.
 * @param summaryNode 'summary' XML node
 */
class TaintSummary(summaryNode: Node) {
    def methods: Seq[MethodSummary] = (summaryNode \\ "methods" \\ "method")
        .map(methodNode => {
            val sig = (methodNode \@ "id")
                .replace("&lt;", "<")
                .replace("&gt;", ">")
            signaturePattern.findFirstMatchIn(sig) match {
                case Some(m) =>
                    val paramTypes: List[FieldType] =
                        if (m.group(3) == "") List()
                        else m.group(3)
                              .split(",")
                              .map(s => stringToFieldType(s.strip()))
                              .toList
                    MethodSummary(
                        stringToReturnType(m.group(1)),
                        m.group(2),
                        paramTypes,
                        methodNode
                    )
                case None =>
                    throw new RuntimeException("couldn't parse the signature of "+sig);
            }
        }).toList

    /**
     * Applies the summary.
     * @param call call java statement
     * @param callStmt call TAC statement
     * @param in fact
     * @return out set of facts
     */
    def compute(call: JavaStatement, callStmt: Call[V], in: TaintFact): Set[TaintFact] = {
        in match {
            /* We do not have any summaries for null facts. */
            case TaintNullFact => Set(in)
            case _ =>
                /* Find the right method, even when overloaded. */
                val methodSummary = methods.find(m => m.methodName == callStmt.name
                    && m.paramTypes
                    .zip(callStmt.descriptor.parameterTypes)
                    .forall(t => t._1 == t._2))
                methodSummary match {
                    case Some(methodSummary) => methodSummary.compute(call, callStmt, in) + in
                    case None                => Set(in)
                }
        }
    }
}

object TaintSummary {
    /* group 1 = return type, group 2 = method name, group 3 = param list */
    val signaturePattern: Regex = """([a-zA-Z.\[\]]*?) ([a-zA-Z0-9_<>]*?)\(([a-zA-Z.\[\],\s]*?)\)""".r

    /**
     * Converts the type string in Soot's format to the OPAL ObjectType.
     * @param str type string
     * @return ObjectType
     */
    def stringToFieldType(str: String): FieldType = {
        str match {
            case "boolean" => BooleanType
            case "byte"    => ByteType
            case "char"    => CharType
            case "short"   => ShortType
            case "int"     => IntegerType
            case "long"    => ObjectType.Long
            case "float"   => ObjectType.Float
            case "double"  => ObjectType.Double
            case "String"  => ObjectType.String
            case _ =>
                if (str.endsWith("[]"))
                    ArrayType(stringToFieldType(str.substring(0, str.length - 2)))
                else
                    ObjectType(str.replace(".", "/"))
        }
    }

    def stringToReturnType(str: String): Type = {
        str match {
            case "void" => VoidType
            case _      => stringToFieldType(str)
        }
    }
}

/**
 * Represents the summary of a single method.
 * @param returnType return type
 * @param methodName method name
 * @param paramTypes parameter types
 * @param methodNode 'method' XML node
 */
case class MethodSummary(returnType: Type, methodName: String, paramTypes: List[FieldType], methodNode: Node) {
    def flows: Seq[Flow] = methodNode.head.map(flowNode => Flow(flowNode))

    def compute(call: JavaStatement, callStmt: Call[V], in: TaintFact): Set[TaintFact] = {
        flows.flatMap(f =>
            if (f.matchesFrom(callStmt, in))
                f.createTaint(call, callStmt, in)
            else
                Set.empty).toSet
    }

    override def toString: String = s"${returnType.toString} ${methodName}(${paramTypes.mkString(", ")})"
}

/**
 * Represents one summarized flow.
 * @param flowNode 'flow' XML node
 */
case class Flow(flowNode: Node) {
    // only needed if we'd use a on-demand alias analysis
    val isAlias: Boolean = (flowNode \@ "isAlias").equals("true")
    // TODO: how important is type checking?
    val typeChecking: Boolean = (flowNode \@ "typeChecking").equals("true")
    val from: SummaryTaint = nodeToTaint((flowNode \\ "from").head)
    val to: SummaryTaint = nodeToTaint((flowNode \\ "to").head)

    /**
     * Return true if the taint matches the 'from' rule.
     * @param callStmt call TAC statement
     * @param in fact
     * @return Boolean
     */
    def matchesFrom(callStmt: Call[V], in: TaintFact): Boolean = {
        val isStatic = callStmt.receiverOption.isEmpty
        val allParamsWithIndex = callStmt.allParams.zipWithIndex

        from match {
            case ParameterSummaryTaint(summaryIndex) =>
                in match {
                    case Variable(index) =>
                        JavaIFDSProblem.getParameterIndex(allParamsWithIndex, index, isStatic) == summaryIndex
                    /* Summaries do not know array elements. */
                    case ArrayElement(index, _) =>
                        JavaIFDSProblem.getParameterIndex(allParamsWithIndex, index, isStatic) == summaryIndex
                    case _ => false
                }
            case BaseObjectSummaryTaint(summaryFieldName: String) =>
                in match {
                    case InstanceField(index, _, fieldName) =>
                        (JavaIFDSProblem.getParameterIndex(allParamsWithIndex, index, isStatic) == -1
                            && summaryFieldName == fieldName)
                    /* Over-approximation: apply the rule even though if no field is known. */
                    case Variable(index) =>
                        JavaIFDSProblem.getParameterIndex(allParamsWithIndex, index, isStatic) == -1
                    case _ => false
                }
            case _ => false
        }
    }

    /**
     * Return the resulting set of facts after applying the summary.
     * @param call call java statement
     * @param callStmt call TAC statement
     * @param in fact
     * @return Out set of facts
     */
    def createTaint(call: JavaStatement, callStmt: Call[V], in: TaintFact): Set[TaintFact] = {
        to match {
            case ParameterSummaryTaint(summaryIndex: Int) =>
                callStmt.params(summaryIndex).asVar.definedBy.map(i => Variable(i))
            case BaseObjectSummaryTaint(fieldName) =>
                Set(InstanceField(call.index, callStmt.declaringClass.mostPreciseObjectType, fieldName))
            case ReturnSummaryTaint() if call.stmt.isAssignment =>
                Set(Variable(call.index))
            case _ => Set.empty
        }
    }
}

object Flow {
    /**
     * Maps a 'from' or 'to' XML node to an SummaryTaint
     * @param node 'from' or 'to' node
     * @return SummaryTaint
     */
    def nodeToTaint(node: Node): SummaryTaint = {
        // TODO: Fields on returns/parameters
        node \@ "sourceSinkType" match {
            case "Parameter" => ParameterSummaryTaint((node \@ "ParameterIndex").toInt - 2)
            case "Field" =>
                BaseObjectSummaryTaint((node \@ "AccessPath")
                    .split(" ")
                    .last
                    .replace("]", ""))
            case "Return" => ReturnSummaryTaint()
        }
    }
}

trait SummaryTaint
case class ParameterSummaryTaint(idx: Int) extends SummaryTaint
case class BaseObjectSummaryTaint(fieldName: String) extends SummaryTaint
case class ReturnSummaryTaint() extends SummaryTaint
