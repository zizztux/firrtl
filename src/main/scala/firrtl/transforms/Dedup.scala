package firrtl
package transforms

import firrtl.ir._
import firrtl.Mappers._
import firrtl.Annotations._
import firrtl.passes.PassException

// Datastructures
import scala.collection.mutable

// Tags an annotation to be consumed by this pass
case class DedupAnnotation(target: Named) extends Annotation with Loose with Unstable {
  def duplicate(n: Named) = this.copy(target=n)
  def transform = classOf[DedupModules]
}

// Only use on legal Firrtl. Specifically, the restriction of
//  instance loops must have been checked, or else this pass can
//  infinitely recurse
class DedupModules extends Transform {
   def inputForm = HighForm
   def outputForm = HighForm
   def execute(state: CircuitState): CircuitState = state.copy(circuit = run(state.circuit))
   def run(c: Circuit): Circuit = {
      val moduleOrder = mutable.ArrayBuffer[String]()
      val moduleMap = c.modules.foldLeft(Map[String, DefModule]()){(map, m) => map + (m.name -> m)}
      def hasInstance(b: Statement): Boolean = {
        var has = false
        def onStmt(s: Statement): Statement = s map onStmt match {
          case DefInstance(i, n, m) => 
            if(!(moduleOrder contains m)) has = true
            s
          case WDefInstance(i, n, m, t) => 
            if(!(moduleOrder contains m)) has = true
            s
          case _ => s
        }
        onStmt(b)
        has
      }
      def addModule(m: DefModule): DefModule = m match {
        case Module(info, n, ps, b) =>
          if(!hasInstance(b)) moduleOrder += m.name
          m
        case ExtModule(info, n, ps) =>
          moduleOrder += m.name
          m
        case _ => m
      }

      while((moduleOrder.size < c.modules.size)) {
        c.modules.foreach(m => if(!moduleOrder.contains(m.name)) addModule(m))
      }

      // Module body -> Module name
      val dedupModules = mutable.HashMap[String, String]()
      // Old module name -> dup module name
      val dedupMap = mutable.HashMap[String, String]()
      def onModule(m: DefModule): Option[DefModule] = {
        def fixInstance(s: Statement): Statement = s map fixInstance match {
          case DefInstance(i, n, m) => DefInstance(i, n, dedupMap.getOrElse(m, m))
          case WDefInstance(i, n, m, t) => WDefInstance(i, n, dedupMap.getOrElse(m, m), t)
          case x => x
        }

        val mx = m map fixInstance
        val string = mx match {
          case Module(i, n, ps, b) =>
            ps.map(_.serialize).foldLeft(""){(str, p) => str + p} + b.serialize
          case ExtModule(i, n, ps) =>
            ps.map(_.serialize).foldLeft(""){(str, p) => str + p}
        }
        dedupModules.get(string) match {
          case Some(dupname) =>
            dedupMap(mx.name) = dupname
            None
          case None => 
            dedupModules(string) = mx.name
            Some(mx)
        }
      }
      val modulesx = moduleOrder.map(n => onModule(moduleMap(n))).flatMap({case Some(m) => Seq(m) case None => Nil})
      val modulexMap = modulesx.foldLeft(Map[String, DefModule]()){(map, m) => map + (m.name -> m)}
      c.copy(modules=c.modules.flatMap(m => modulexMap.get(m.name) match { case Some(x) => Seq(x) case None => Nil}))
   }
}
