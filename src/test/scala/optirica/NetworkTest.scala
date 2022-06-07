
package optirica

import org.scalacheck.Properties

import ap.SimpleAPI
import ap.parser._
import IExpression.{Sort, Predicate}
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction

import lazabs.horn.bottomup.HornClauses
import HornClauses._

import lattopt.{PowerSetLattice, Algorithms, SeededRandomDataSource}

object NetworkTest extends Properties("NetworkTest") {

  def networkClauses = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      val typ  = createConstant("typ")
      val dst  = createConstant("dst")

      val t1 = createRelation("t1", Seq(Sort.Integer, Sort.Integer))
      val t2 = createRelation("t2", Seq(Sort.Integer, Sort.Integer))
      val t3 = createRelation("t3", Seq(Sort.Integer, Sort.Integer))
      val t4 = createRelation("t4", Seq(Sort.Integer, Sort.Integer))

      val a1 = createRelation("a1", Seq(Sort.Integer, Sort.Integer))
      val a2 = createRelation("a2", Seq(Sort.Integer, Sort.Integer))
      val a3 = createRelation("a3", Seq(Sort.Integer, Sort.Integer))
      val a4 = createRelation("a4", Seq(Sort.Integer, Sort.Integer))

      val c1 = createRelation("c1", Seq(Sort.Integer, Sort.Integer))
      val c2 = createRelation("c2", Seq(Sort.Integer, Sort.Integer))

      val drop = createRelation("drop", Seq(Sort.Integer, Sort.Integer))

      import ap.parser.IExpression._

      val ingressCls = {
        List(
          (t1(dst, typ) :- (typ === 0, (dst === 2 ||| dst === 3 ||| dst === 4))),
          (t2(dst, typ) :- (typ > 0, typ < 8, (dst === 1 ||| dst === 3 ||| dst === 4))),
          (t3(dst, typ) :- (typ > 0, typ < 8, (dst === 1 ||| dst === 2 ||| dst === 4))),
          (t4(dst, typ) :- (typ > 0, typ < 8, (dst === 1 ||| dst === 2 ||| dst === 3)))
        )
      }

      val networkCls = {
        List(
          // --------- T1 rules ---------
          ( a1(dst,typ)  :- (t1(dst,typ), dst =/= 1 )),
          ( a2(dst,typ)  :- (t1(dst,typ), dst =/= 1 )),
          ( drop(dst,typ)  :- (t1(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- T2 rules ---------
          ( a1(dst,typ)  :- (t2(dst,typ), dst =/= 2 )),
          ( a2(dst,typ)  :- (t2(dst,typ), dst =/= 2 )),
          ( drop(dst,typ)  :- (t2(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- T3 rules ---------
          ( a3(dst,typ)  :- (t3(dst,typ), dst =/= 3 )),
          ( a4(dst,typ)  :- (t3(dst,typ), dst =/= 3 )),
          ( drop(dst,typ)  :- (t3(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- T4 rules ---------
          ( a4(dst,typ)  :- (t4(dst,typ), dst =/= 4 )),
          ( drop(dst,typ)  :- (t4(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- A1 rules ---------
          ( c1(dst,typ)  :- (a1(dst,typ), dst =/= 1, dst =/= 2 )),
          ( c2(dst,typ)  :- (a1(dst,typ), dst =/= 1, dst =/= 2 )),
          ( t1(dst,typ)  :- (a1(dst,typ), dst === 1 )),
          ( t2(dst,typ)  :- (a1(dst,typ), dst === 2 )),
          ( drop(dst,typ)  :- (a1(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- A2 rules ---------
          ( c1(dst,typ)  :- (a2(dst,typ), dst =/= 1, dst =/= 2 )),
          ( c2(dst,typ)  :- (a2(dst,typ), dst =/= 1, dst =/= 2 )),
          ( t1(dst,typ)  :- (a2(dst,typ), dst === 1 )),
          ( t2(dst,typ)  :- (a2(dst,typ), dst === 2 )),
          ( drop(dst,typ)  :- (a2(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- A3 rules ---------
          ( c1(dst,typ)  :- (a3(dst,typ), dst =/= 3 )),
          ( c2(dst,typ)  :- (a3(dst,typ), dst =/= 3 )),
          ( t3(dst,typ)  :- (a3(dst,typ), dst === 3 )),
          ( drop(dst,typ)  :- (a3(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- A4 rules ---------
          ( c1(dst,typ)  :- (a4(dst,typ), dst =/= 3, dst =/= 4 )),
          ( c2(dst,typ)  :- (a4(dst,typ), dst =/= 3, dst =/= 4 )),
          ( t3(dst,typ)  :- (a4(dst,typ), dst === 3 )),
          ( t4(dst,typ)  :- (a4(dst,typ), dst === 4 /* , dstFilter(dst), typFilter(typ) */)), // filter typ = 0
          ( drop(dst,typ)  :- (a4(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- C1 rules ---------
          ( a3(dst,typ)  :- (c1(dst,typ), (dst === 3 ||| dst === 4) )),
          ( a4(dst,typ)  :- (c1(dst,typ), (dst === 3 ||| dst === 4), (typ =/= 0) )),
          ( a1(dst,typ)  :- (c1(dst,typ), (dst === 1 ||| dst === 2) )),
          ( a2(dst,typ)  :- (c1(dst,typ), (dst === 1 ||| dst === 2) )),
          ( drop(dst,typ)  :- (c1(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) )),
          // --------- C2 rules ---------
          ( a3(dst,typ)  :- (c2(dst,typ), (dst === 3 ||| dst === 4) )),
          ( a4(dst,typ)  :- (c2(dst,typ), (dst === 3 ||| dst === 4) )),
          ( a1(dst,typ)  :- (c2(dst,typ), (dst === 1 ||| dst === 2) )),
          ( a2(dst,typ)  :- (c2(dst,typ), (dst === 1 ||| dst === 2) )),
          ( drop(dst,typ)  :- (c2(dst,typ), (!(dst >= 1) ||| !(dst <= 4) ||| !(typ >= 0) ||| !(typ <= 7)) ))
        )
      }

      val propertyCls = {
        List(
          (false :- (t4(dst, typ), (typ === 0))), // No H1 traffic at T4
          (false :- (drop(dst, typ), (typ === 0))) // No H1 traffic at drop
        )
      }

      (ingressCls, networkCls, propertyCls)
    }
  }

  /**
   * Compute maximally-satisfiable subsets of the network clauses.
   */
  property("Network verification: MaxSAT") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      val (ingressCls, networkCls, propertyCls) = networkClauses

      import ap.parser.IExpression._

      val flags =
        for (n <- 0 until networkCls.size) yield createRelation("f" + n, Seq())

      val instrNetworkCls =
        for ((Clause(head, body, constraint), f) <- networkCls zip flags)
        yield Clause(head, body ++ List(f()), constraint)

      val clauses =
        ingressCls ++ instrNetworkCls ++ propertyCls

      import Conjunction.{TRUE, FALSE}

      def set2map(s : Set[Predicate]) =
        (for (f <- flags) yield (f -> (if (s(f)) TRUE else FALSE))).toMap

      val mapLattice =
        for (s <- PowerSetLattice(flags)) yield set2map(s)

      val satLattice =
        ClauseSatLattice(mapLattice, clauses, flags.toSet)

      val seed = 123
      implicit val randomData = new SeededRandomDataSource(seed)

      val optFeasible =
        for (bv <- Algorithms.optimalFeasibleObjects(satLattice)(
                                                     satLattice.bottom))
        yield satLattice.getLabel(bv)

      optFeasible.size == 2 // there should be two solutions
    }
  }

  /**
   * Compute filters for the clause t4(dst,typ) :- a4(dst,typ), dst === 4
   */
  property("Network verification: bit-wise dst/type-filter") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      val (ingressCls, networkCls, propertyCls) = networkClauses

      val dstFilter = createRelation("dstFilter", Seq(Sort.Integer))
      val typFilter = createRelation("typFilter", Seq(Sort.Integer))

      val updatedClause = {
        import ap.parser.IExpression._
        val c@Clause(head@IAtom(_, Seq(dst, typ)), body, constraint) =
          networkCls(28)
        Clause(head, body ++ List(dstFilter(dst), typFilter(typ)), constraint)
      }

      val instrNetworkCls = networkCls.updated(28, updatedClause)

      val clauses =
        ingressCls ++ instrNetworkCls ++ propertyCls

      import TerForConvenience._
      implicit val o = order

      val dstLattice =
        for (s <- PowerSetLattice(1 to 4))
        yield Map(dstFilter -> disjFor(for (t <- s) yield v(0) === t))
      val typLattice =
        for (s <- PowerSetLattice(0 to 7))
        yield Map(typFilter -> disjFor(for (t <- s) yield v(0) === t))

      val mapLattice =
        (for (m1 <- dstLattice; m2 <- typLattice) yield (m1 ++ m2)).
          mapScore { p => p._1 + p._2 }

      val satLattice =
        ClauseSatLattice(mapLattice, clauses, Set(dstFilter, typFilter))

      val seed = 123
      implicit val randomData = new SeededRandomDataSource(seed)

      val optFeasible =
        for (bv <- Algorithms.optimalFeasibleObjects(satLattice)(
                                                     satLattice.bottom))
        yield satLattice.getLabel(bv)

      optFeasible.size == 2 // there should be two solutions: either filter dst == 4 or typ == 0
    }
  }

}
