
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

object ClauseSatTest extends Properties("ClauseSatTest") {

  property("Bitset Sat Lattice") = (0 until 3) forall { seed =>
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      val x  = createConstant("x")
      val y  = createConstant("y")
      val n  = createConstant("n")

      val I  = createRelation("I", Seq(Sort.Integer, Sort.Integer, Sort.Integer))
      val f0 = createRelation("f0", Seq())
      val f1 = createRelation("f1", Seq())
      val f2 = createRelation("f2", Seq())
      val f3 = createRelation("f3", Seq())

      val flags = List(f0, f1, f2, f3)

      val clauses = {
        import ap.parser.IExpression._
        List(
          I(0, 0, n)         :- f0(),
          I(x + 1, y + 1, n) :- (I(x, y, n), f1(), y < n),
          I(x + 2, y + 1, n) :- (I(x, y, n), f2(), y < n),
          false              :- (I(x, y, n), f3(), x > 2*n)
        )
      }

      import Conjunction.{TRUE, FALSE}

      def set2map(s : Set[Predicate]) =
        (for (f <- flags) yield (f -> (if (s(f)) TRUE else FALSE))).toMap

      val setLattice =
        PowerSetLattice(flags).withScore(s =>
          s.size + (if (s contains f0) 1 else 0))

      val mapLattice =
        for (s <- setLattice) yield set2map(s)

      val satLattice =
        ClauseSatLattice(mapLattice, clauses, flags.toSet)

      implicit val randomData = new SeededRandomDataSource(seed)

      val maxFeasible =
        (for (bv <- Algorithms.maximalFeasibleObjects(
                satLattice)(
                satLattice.bottom))
         yield satLattice.getLabel(bv)).toSet

      assert(maxFeasible == Set(set2map(Set(f0, f1, f2)), set2map(Set(f1, f2, f3))))

      val optFeasible =
        (for (bv <- Algorithms.optimalFeasibleObjects(
                satLattice)(
                satLattice.bottom))
         yield satLattice.getLabel(bv)).toSet

      assert(optFeasible == Set(set2map(Set(f0, f1, f2))))

      true
    }
  }

  property("Network Clauses") = {
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

      val ingressCls = {
        import ap.parser.IExpression._
        List(
          (t1(dst, typ) :- (typ === 0, (dst === 2 ||| dst === 3 ||| dst === 4))),
          (t2(dst, typ) :- (typ > 0, typ < 8, (dst === 1 ||| dst === 3 ||| dst === 4))),
          (t3(dst, typ) :- (typ > 0, typ < 8, (dst === 1 ||| dst === 2 ||| dst === 4))),
          (t4(dst, typ) :- (typ > 0, typ < 8, (dst === 1 ||| dst === 2 ||| dst === 3)))
        )
      }

      val networkCls = {
        import ap.parser.IExpression._
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
          ( t4(dst,typ)  :- (a4(dst,typ), dst === 4 )), // filter typ = 0
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
        import ap.parser.IExpression._
        List(
          (false :- (t4(dst, typ), (typ === 0))), // No H1 traffic at T4
          (false :- (drop(dst, typ), (typ === 0))) // No H1 traffic at drop
        )
      }

      true //To-do
    }
  }

}
