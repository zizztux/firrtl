// See LICENSE for license details.

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._

import annotation.tailrec

object CommonSubexpressionElimination extends Pass {
  private def cseOnce(s: Statement): (Statement, Long) = {
    var nEliminated = 0L
    val expressions = collection.mutable.HashMap[MemoizedHash[Expression], String]()
    val nodes = collection.mutable.HashMap[String, Expression]()

    //def recordNodes(s: Statement): Statement = s match {
    //  case x: DefNode =>
    //    //println(s"Recording ${x.serialize}")
    //    //println(s"  ${x.value}")
    //    nodes(x.name) = x.value
    //    expressions.getOrElseUpdate(x.value, x.name)
    //    x
    //  case _ => s map recordNodes
    //}

    def eliminateNodeRef(e: Expression): Expression = e match {
      case WRef(name, tpe, kind, gender) => nodes get name match {
        case Some(expression) => expressions get expression match {
          case Some(cseName) if cseName != name =>
            nEliminated += 1
            WRef(cseName, tpe, kind, gender)
          case _ => e
        }
        case _ => e
      }
      case _ => e map eliminateNodeRef
    }

    def eliminateNodeRefs(s: Statement): Statement = {
      s map eliminateNodeRef match {
        case x: DefNode =>
          nodes(x.name) = x.value
          expressions.getOrElseUpdate(x.value, x.name)
          x
        case other => other map eliminateNodeRefs map eliminateNodeRef
      }
    }

    //recordNodes(s)
    (eliminateNodeRefs(s), nEliminated)
  }

  //@tailrec
  private def cse(s: Statement, count: Long = 1): (Statement, Long) = {
    val (res, n) = cseOnce(s)
    //println(res.serialize)
    //if (n > 0) cse(res, count + 1) else (res, count)
    (res, count)
  }

  def run(c: Circuit): Circuit = {
    val modulesx = c.modules.map {
      case m: ExtModule => m
      case m: Module =>
        val (newBody, count) = cse(m.body)
        println(s"For Module ${m.name}, ran cse $count times")
        Module(m.info, m.name, m.ports, newBody)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
