
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
          I(0, 0, n)         :-             (f0(), n > 0),
          I(x + 1, y + 1, n) :- (I(x, y, n), f1(), y < n),
          I(x + 2, y + 1, n) :- (I(x, y, n), f2(), y < n),
          false              :- (I(x, y, n), f3(), x >= 2*n)
        )
      }

      import Conjunction.{TRUE, FALSE}

      def set2map(s : Set[Predicate]) =
        (for (f <- flags) yield (f -> (if (s(f)) TRUE else FALSE))).toMap

      val setLattice =
        PowerSetLattice(flags).withScore(s =>
          (s.iterator map {
             case `f0` => 2
             case `f1` => 1
             case `f2` => 1
             case `f3` => 2
           }).sum)

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

      assert(maxFeasible ==
               Set(set2map(Set(f0, f1, f2)),
                   set2map(Set(f1, f2, f3)),
                   set2map(Set(f0, f1, f3))))

      val optFeasible =
        (for (bv <- Algorithms.optimalFeasibleObjects(
                satLattice)(
                satLattice.bottom))
         yield satLattice.getLabel(bv)).toSet

      assert(optFeasible == Set(set2map(Set(f0, f1, f3))))

      true
    }
  }

}
