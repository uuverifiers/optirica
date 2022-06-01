/**
 * Copyright (c) 2022 Hossein Hojjat, Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package optirica

import lattopt.{OptLattice, CachedFilteredLatticeWithBounds}

import lazabs.horn.bottomup.{HornClauses, IncrementalHornPredAbs, Util,
                             DisjInterpolator, DagInterpolator, NormClause, CEGAR}
import Util._
import DisjInterpolator._

import ap.parser._
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

object ClauseLattices {
    def cexSubstSyms[CC <% HornClauses.ConstraintClause]
                    (cex : Dag[(IAtom, CC)],
                     substitutableSyms : Set[Predicate]) : Set[Predicate] =
      (for ((_, clause) <- cex.iterator;
            p <- clause.predicates.iterator;
            if substitutableSyms contains p)
       yield p).toSet

    def solSubstSyms[CC <% HornClauses.ConstraintClause]
                    (sol                  : Map[Predicate, Conjunction],
                     parameterisedClauses : Iterable[CC],
                     substitutableSyms    : Set[Predicate]) : Set[Predicate] =
      (for (clause <- parameterisedClauses.iterator;
            trivial = {
              (!(substitutableSyms contains clause.head.predicate) &&
                 clause.head.predicate != HornClauses.FALSE &&
                 sol(clause.head.predicate).isTrue) ||
              (clause.body exists { lit =>
                 !(substitutableSyms contains lit.predicate) &&
                 sol(lit.predicate).isFalse })
            };
            clausePreds = if (trivial) Set() else clause.predicates;
            pred <- clausePreds.iterator;
            if substitutableSyms contains pred)
       yield pred).toSet
}

object ClauseSatLattice {

  import ClauseLattices._

  def apply[CC <% HornClauses.ConstraintClause, Score](
            lattice              : OptLattice[Map[Predicate, Conjunction], Score],
            parameterisedClauses : Iterable[CC],
            substitutableSyms    : Set[Predicate],
            initialPredicates    : Map[Predicate, Seq[IFormula]] =
              Map(),
            predicateGenerator   : Dag[AndOrNode[NormClause, Unit]] =>
                                     Either[Seq[(Predicate, Seq[Conjunction])],
                                            Dag[(IAtom, NormClause)]] =
              DagInterpolator.interpolatingPredicateGenCEXAndOr _,
            counterexampleMethod : CEGAR.CounterexampleMethod.Value =
              CEGAR.CounterexampleMethod.FirstBestShortest)
         : OptLattice[Map[Predicate, Conjunction], Score] = {

    val solver = new IncrementalHornPredAbs(parameterisedClauses,
                                            initialPredicates,
                                            substitutableSyms,
                                            predicateGenerator,
                                            counterexampleMethod)

    lattice.filterWithBounds {
      (subst, optFeasible, optInfeasible) => {
        solver.checkWithSubstitution(subst) match {

          case Left(sol) => {
            val relevantSubstSyms =
              solSubstSyms(sol, parameterisedClauses, substitutableSyms)
            optFeasible(subst2 =>
              relevantSubstSyms forall { p => subst(p) == subst2(p) })
          }

          case Right(cex) => {
            val usedSubstSyms =
              cexSubstSyms(cex, substitutableSyms)
            optInfeasible(subst2 =>
              usedSubstSyms forall { p => subst(p) == subst2(p) })
          }

        }
      }
    }

  }
}

object ClauseUnsatLattice {

  import ClauseLattices._

  def apply[CC <% HornClauses.ConstraintClause, Score](
            lattice              : OptLattice[Map[Predicate, Conjunction], Score],
            parameterisedClauses : Iterable[CC],
            substitutableSyms    : Set[Predicate],
            initialPredicates    : Map[Predicate, Seq[IFormula]] =
              Map(),
            predicateGenerator   : Dag[AndOrNode[NormClause, Unit]] =>
                                     Either[Seq[(Predicate, Seq[Conjunction])],
                                            Dag[(IAtom, NormClause)]] =
              DagInterpolator.interpolatingPredicateGenCEXAndOr _,
            counterexampleMethod : CEGAR.CounterexampleMethod.Value =
              CEGAR.CounterexampleMethod.FirstBestShortest)
        : OptLattice[Map[Predicate, Conjunction], Score] = {

    val solver = new IncrementalHornPredAbs(parameterisedClauses,
                                            initialPredicates,
                                            substitutableSyms,
                                            predicateGenerator,
                                            counterexampleMethod)

    lattice.filterWithBounds {
      (subst, optFeasible, optInfeasible) => {
        solver.checkWithSubstitution(subst) match {

          case Left(sol) => {
            val relevantSubstSyms =
              solSubstSyms(sol, parameterisedClauses, substitutableSyms)
            optInfeasible(subst2 =>
              relevantSubstSyms forall { p => subst(p) == subst2(p) })
          }

          case Right(cex) => {
            val usedSubstSyms =
              cexSubstSyms(cex, substitutableSyms)
            optFeasible(subst2 =>
              usedSubstSyms forall { p => subst(p) == subst2(p) })
          }

        }
      }
    }

  }
}
