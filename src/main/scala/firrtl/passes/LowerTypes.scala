/*
Copyright (c) 2014 - 2016 The Regents of the University of
California (Regents). All Rights Reserved.  Redistribution and use in
source and binary forms, with or without modification, are permitted
provided that the following conditions are met:
   * Redistributions of source code must retain the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer.
   * Redistributions in binary form must reproduce the above
     copyright notice, this list of conditions and the following
     two paragraphs of disclaimer in the documentation and/or other materials
     provided with the distribution.
   * Neither the name of the Regents nor the names of its contributors
     may be used to endorse or promote products derived from this
     software without specific prior written permission.
IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT,
SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS,
ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF
REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF
ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION
TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
MODIFICATIONS.
*/

package firrtl.passes

import firrtl._
import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import MemPortUtils.memPortField

/** Removes all aggregate types from a [[firrtl.ir.Circuit]]
  *
  * @note Assumes [[firrtl.ir.SubAccess]]es have been removed
  * @note Assumes [[firrtl.ir.Connect]]s and [[firrtl.ir.IsInvalid]]s only operate on [[firrtl.ir.Expression]]s of ground type
  * @example
  * {{{
  *   wire foo : { a : UInt<32>, b : UInt<16> }
  * }}} lowers to
  * {{{
  *   wire foo_a : UInt<32>
  *   wire foo_b : UInt<16>
  * }}}
  */
object LowerTypes extends Pass {
  def name = "Lower Types"

  /** Delimiter used in lowering names */
  val delim = "_"
  /** Expands a chain of referential [[firrtl.ir.Expression]]s into the equivalent lowered name
    * @param e [[firrtl.ir.Expression]] made up of _only_ [[firrtl.WRef]], [[firrtl.WSubField]], and [[firrtl.WSubIndex]]
    * @return Lowered name of e
    */
  def loweredName(e: Expression): String = e match {
    case e: WRef => e.name
    case e: WSubField => s"${loweredName(e.exp)}$delim${e.name}"
    case e: WSubIndex => s"${loweredName(e.exp)}$delim${e.value}"
  }
  def loweredName(s: Seq[String]): String = s mkString delim

  private case class LowerTypesException(msg: String) extends FIRRTLException(msg)
  private def error(msg: String)(info: Info, mname: String) =
    throw LowerTypesException(s"$info: [module $mname] $msg")

  // TODO Improve? Probably not the best way to do this
  def splitMemRef(e1: Expression): (WRef, WRef, WRef, Option[Expression]) = {
    val (mem, tail1) = splitRef(e1)
    val (port, tail2) = splitRef(tail1)
    tail2 match {
      case e2: WRef =>
        (mem, port, e2, None)
      case _ =>
        val (field, tail3) = splitRef(tail2)
        (mem, port, field, Some(tail3))
    }
  }

  type GroundMemSet = collection.mutable.HashSet[String]

  def updateMemConnects(g: Gender, mname: String)(s: Statement): Statement = s match {
    case Connect(info, loc, expr) => g match {
      case FEMALE =>
        DefNode(info, loweredName(loc), expr)
      case MALE =>
        Connect(info, loc, lowerTypesExp(new GroundMemSet, info, mname)(expr))
    }
    case s => s map updateMemConnects(g, mname)
  }

  val isDataOrMask = Set("data", "mask", "rdata", "wdata", "wmask")
  def lowerTypesExp(groundMems: GroundMemSet,
      info: Info, mname: String)(e: Expression): Expression = e match {
    case (_: WSubField | _: WSubIndex) => kind(e) match {
      case InstanceKind =>
        val (root, tail) = splitRef(e)
        val name = loweredName(tail)
        WSubField(root, name, e.tpe, gender(e))
      case MemKind =>
        val (mem, port, field, tail) = splitMemRef(e)
        if (groundMems(mem.name) || !isDataOrMask(field.name)) e 
        else WRef(loweredName(e), e.tpe, WireKind, gender(e))
      case _ => WRef(loweredName(e), e.tpe, kind(e), gender(e))
    }
    case e: Mux => e map lowerTypesExp(groundMems, info, mname)
    case e: ValidIf => e map lowerTypesExp(groundMems, info, mname)
    case e: DoPrim => e map lowerTypesExp(groundMems, info, mname)
    case _ => e
  }

  def lowerTypesStmt(groundMems: GroundMemSet,
      minfo: Info, mname: String)(s: Statement): Statement = {
    val info = get_info(s) match {case NoInfo => minfo case x => x}
    s map lowerTypesStmt(groundMems, info, mname) match {
      case s: DefWire => s.tpe match {
        case _: GroundType => s
        case _ => Block(create_exps(s.name, s.tpe) map (
          e => DefWire(s.info, loweredName(e), e.tpe)))
      }
      case s: DefRegister => s.tpe match {
        case _: GroundType => s map lowerTypesExp(groundMems, info, mname)
        case _ =>
          val es = create_exps(s.name, s.tpe)
          val inits = create_exps(s.init) map lowerTypesExp(groundMems, info, mname)
          val clock = lowerTypesExp(groundMems, info, mname)(s.clock)
          val reset = lowerTypesExp(groundMems, info, mname)(s.reset)
          Block(es zip inits map { case (e, i) =>
            DefRegister(s.info, loweredName(e), e.tpe, clock, reset, i)
          })
      }
      // Could instead just save the type of each Module as it gets processed
      case s: WDefInstance => s.tpe match {
        case t: BundleType =>
          val fieldsx = t.fields flatMap (f =>
            create_exps(WRef(f.name, f.tpe, ExpKind, times(f.flip, MALE))) map (
              // Flip because inst genders are reversed from Module type
              e => Field(loweredName(e), swap(to_flip(gender(e))), e.tpe)))
          WDefInstance(s.info, s.name, s.module, BundleType(fieldsx))
        case _ => error("WDefInstance type should be Bundle!")(info, mname)
      }
      case s: DefMemory => s.dataType match {
        case _: GroundType => groundMems += s.name ; s
        case _ =>
          val mem = s copy (dataType = UIntType(IntWidth(bitWidth(s.dataType))))
          val nodes = (mem.readers map { r =>
            fromBits(memPortField(s, r, "data"), memPortField(mem, r, "data"))
          }) ++ (mem.readwriters map { rw =>
            fromBits(memPortField(s, rw, "rdata"), memPortField(mem, rw, "rdata"))
          }) map updateMemConnects(FEMALE, mname)
          val mt = UIntType(IntWidth(bitWidth(createMask(s.dataType))))
          val wireConnects = (mem.writers flatMap { w =>
            val wires = Seq(memPortField(s, w, "data"), memPortField(s, w, "mask")) flatMap (
              f => create_exps(f) map (e => DefWire(info, loweredName(e), e.tpe)))
            val mask = memPortField(mem, w, "mask") copy (tpe = mt)
            wires ++ Seq(
              Connect(info, mask, toBits(memPortField(s, w, "mask"))),
              Connect(info, memPortField(mem, w, "data"), toBits(memPortField(s, w, "data"))
            ))
          }) ++ (mem.readwriters flatMap { rw =>
            val wires = Seq(memPortField(s, rw, "wdata"), memPortField(s, rw, "wmask")) flatMap (
              f => create_exps(f) map (e => DefWire(info, loweredName(e), e.tpe)))
            val wmask = memPortField(mem, rw, "wmask") copy (tpe = mt)
            wires ++ Seq(
              Connect(info, wmask, toBits(memPortField(s, rw, "wmask"))),
              Connect(info, memPortField(mem, rw, "wdata"), toBits(memPortField(s, rw, "wdata"))
            ))
          }) map updateMemConnects(MALE, mname)
          Block(mem +: (nodes ++ wireConnects))
      }
      case s: DefNode =>
        // wire foo : { a , b }
        // node x = foo
        // node y = x.a
        //  ->
        // node x_a = foo_a
        // node x_b = foo_b
        // node y = x_a
        val names = create_exps(s.name, s.value.tpe) map lowerTypesExp(groundMems, info, mname)
        val exps = create_exps(s.value) map lowerTypesExp(groundMems, info, mname)
        Block(names zip exps map { case (n, e) => DefNode(info, loweredName(n), e) })
      case s: IsInvalid => kind(s.expr) match {
        case MemKind =>
          val (mem, port, field, tail) = splitMemRef(s.expr)
          if (groundMems(mem.name) || !isDataOrMask(field.name)) s else EmptyStmt
        case _ => s map lowerTypesExp(groundMems, info, mname)
      }
      case s => s map lowerTypesExp(groundMems, info, mname)
    }
  }

  def lowerTypes(m: DefModule): DefModule = {
    val groundMems = new GroundMemSet
    // Lower Ports
    val portsx = m.ports flatMap { p =>
      val exps = create_exps(WRef(p.name, p.tpe, PortKind, to_gender(p.direction)))
      exps map (e => Port(p.info, loweredName(e), to_dir(gender(e)), e.tpe))
    }
    m match {
      case m: ExtModule =>
        m copy (ports = portsx)
      case m: Module =>
        m copy (ports = portsx) map lowerTypesStmt(groundMems, m.info, m.name)
    }
  }

  def run(c: Circuit): Circuit = c copy (modules = (c.modules map lowerTypes))
}

