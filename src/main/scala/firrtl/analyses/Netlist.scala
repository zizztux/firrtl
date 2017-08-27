package firrtl.analyses

import scala.collection.mutable

import firrtl._
import firrtl.ir._
import firrtl.graph._
import firrtl.Utils._
import firrtl.Mappers._


/** A class representing the instance hierarchy of a working IR Circuit
  *
  * @constructor constructs an instance graph from a Circuit
  * @param c the Circuit to analyze
  * @param includeSubhierarchies Keep track of module chains not connected to the top.
  *  Each non-connected module will be treated as a potential top-level in its
  *  own right in the resulting instanceGraph.
  */
class InstanceGraph(c: Circuit, includeSubhierarchies: Boolean = true) {

  private def collectInstances(insts: mutable.Set[WDefInstance])(s: Statement): Statement = s match {
    case i: WDefInstance =>
      insts += i
      i
    case _ =>
      s map collectInstances(insts)
  }

  private val moduleMap = c.modules.map({m => (m.name,m) }).toMap
  private val childInstances =
    new mutable.HashMap[String,mutable.Set[WDefInstance]]
  for (m <- c.modules) {
    childInstances(m.name) = new mutable.HashSet[WDefInstance]
    m map collectInstances(childInstances(m.name))
  }
  private val instanceGraph = new MutableDiGraph[WDefInstance]
  private val instanceQueue = new mutable.Queue[WDefInstance]
  private val topInstance = WDefInstance(c.main,c.main) // top instance
  instanceQueue.enqueue(topInstance)

  // Used to keep track of modules not connected to the top.
  private var modules = mutable.HashMap() ++ moduleMap

  private def processInstanceQueue(): Unit = {
    while (!instanceQueue.isEmpty) {
      val current = instanceQueue.dequeue
      instanceGraph.addVertex(current)
      modules.remove(current.module)
      for (child <- childInstances(current.module)) {
        if (!instanceGraph.contains(child)) {
          instanceQueue.enqueue(child)
        }
        instanceGraph.addEdge(current,child)
      }
    }
  }

  processInstanceQueue()
  // If we want to include the remaining modules, add them to the graph.
  if (includeSubhierarchies) {
    for ((name, m) <- modules) {
      // Treat each of the leftover modules as a potential top-level.
      instanceQueue.enqueue(WDefInstance(name, name))
      processInstanceQueue()
    }
  }

  /** A directed graph showing the instance dependencies among modules
    * in the circuit. Every WDefInstance of a module has an edge to
    * every WDefInstance arising from every instance statement in
    * that module.
    */
  lazy val graph = DiGraph(instanceGraph)

  /** A list of absolute paths (each represented by a Seq of instances)
    * of all module instances in the Circuit.
    */
  lazy val fullHierarchy = graph.pathsInDAG(topInstance)

  /** Finds the absolute paths (each represented by a Seq of instances
    * representing the chain of hierarchy) of all instances of a
    * particular module.
    * 
    * @param module the name of the selected module
    * @return a Seq[Seq[WDefInstance]] of absolute instance paths
    */
  def findInstancesInHierarchy(module: String): Seq[Seq[WDefInstance]] = {
    val instances = graph.getVertices.filter(_.module == module).toSeq
    instances flatMap { i => fullHierarchy(i) }
  }

}

