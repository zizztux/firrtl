package firrtl
package transforms

import firrtl.ir._
import firrtl.Mappers._
import firrtl.Annotations._
import firrtl.passes.PassException

// Datastructures
import scala.collection.mutable

// Only use on legal Firrtl. Specifically, the restriction of
//  instance loops must have been checked, or else this pass can
//  infinitely recurse
object DedupModules extends Transform {
   val inlineDelim = "$"
   def name = this.getClass.getSimpleName
   def execute(circuit: Circuit, annotationMap: AnnotationMap): TransformResult = TransformResult(run(circuit), None, None)
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
        case e: ExtModule =>
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
        def fixPorts(p: Port): Port = p copy (info = NoInfo)
        def fixStatements(s: Statement): Statement = s map fixStatements match {
          case DefInstance(_, n, m) => DefInstance(NoInfo, n, dedupMap.getOrElse(m, m))
          case WDefInstance(_, n, m, t) => WDefInstance(NoInfo, n, dedupMap.getOrElse(m, m), t)
          // TODO: unfortunately [copy] doesn't work for HasInfo
          // better way to handle this?
          // case x: HasInfo => x copy (info = NoInfo)
          case x: DefWire => x copy (info = NoInfo)
          case x: DefNode => x copy (info = NoInfo)
          case x: DefRegister => x copy (info = NoInfo)
          case x: DefMemory => x copy (info = NoInfo)
          case x: Conditionally => x copy (info = NoInfo)
          case x: PartialConnect => x copy (info = NoInfo)
          case x: Connect => x copy (info = NoInfo)
          case x: IsInvalid => x copy (info = NoInfo)
          case x: Attach => x copy (info = NoInfo)
          case x: Stop => x copy (info = NoInfo)
          case x: Print => x copy (info = NoInfo)
          case x => x
        }

        val mx = m map fixPorts map fixStatements
        val string = mx match {
          case Module(_, n, ps, b) =>
            ps.map(_.serialize).foldLeft(""){(str, p) => str + p} + b.serialize
          case ExtModule(_, n, ps, dn, p) =>
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
