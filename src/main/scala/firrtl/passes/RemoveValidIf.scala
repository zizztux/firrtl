// See LICENSE for license details.

package firrtl
package passes
import firrtl.Mappers._
import firrtl.ir._

/** Remove ValidIf and replace IsInvalid with a connection to zero */
object RemoveValidIf extends Pass {
  // Recursive. Removes ValidIfs
  private def onExp(e: Expression): Expression = {
    e map onExp match {
      case ValidIf(_, value, _) => value
      case x => x
    }
  }
  // Recursive. Replaces IsInvalid with connecting zero
  private def onStmt(s: Statement): Statement = s map onStmt map onExp match {
    case IsInvalid(info, loc) => Connect(info, loc, Utils.zero)
    case other => other
  }

  private def onModule(m: DefModule): DefModule = {
    m match {
      case m: Module => Module(m.info, m.name, m.ports, onStmt(m.body))
      case m: ExtModule => m
    }
  }

  def run(c: Circuit): Circuit = Circuit(c.info, c.modules.map(onModule), c.main)
}
