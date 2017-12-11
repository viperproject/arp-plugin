/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter.{ContextC, StrategyBuilder}
import viper.silver.plugin.ARPPlugin.ARPContext
import viper.silver.verifier.errors.{AssertFailed, Internal}
import viper.silver.verifier.reasons.FeatureUnsupported

class ARPPluginWands(plugin: ARPPlugin) {

  def handleApply(input: Program, a: Apply, ctx: ContextC[Node, ARPContext]): Node = {
    Seqn(
      plugin.breathe.splitBreathing(a.exp.left, Some(false), {
        case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
          val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
          if (normalized.isDefined) {
            if (normalized.get.wildcard.isDefined) {
              plugin.reportError(Internal(a, FeatureUnsupported(a, "Rdc is not allowed in wands")))
              Seq(Assert(BoolLit(b = false)())())
            } else {
              plugin.breathe.generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = true, ctx)(a.pos, a.info, NodeTrafo(a))
            }
          } else {
            Seq(Assert(BoolLit(b = false)())())
          }
        case _ => Seq()
      }) ++
        Seq[Stmt](ctx.noRec(a)) ++
        plugin.breathe.splitBreathing(a.exp.right, Some(true), {
          case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
            if (normalized.isDefined) {
              if (normalized.get.wildcard.isDefined) {
                plugin.reportError(Internal(a, FeatureUnsupported(a, "Rdc is not allowed in wands")))
                Seq(Assert(BoolLit(b = false)())())
              } else {
                plugin.breathe.generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = false, ctx)(a.pos, a.info, NodeTrafo(a))
              }
            } else {
              Seq(Assert(BoolLit(b = false)())())
            }
          case _ => Seq()
        }),
      Seq()
    )(a.pos, a.info)
  }

  def handlePackage(input: Program, p: Package, ctx: ContextC[Node, ARPContext]): Node = {
    // TODO: Log proof script

    Seqn(
      plugin.breathe.splitBreathing(p.wand.right, Some(false), {
        case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
          val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
          if (normalized.isDefined) {
            if (normalized.get.wildcard.isDefined) {
              plugin.reportError(Internal(p, FeatureUnsupported(p, "Rdc is not allowed in wands")))
              Seq(Assert(BoolLit(b = false)())())
            } else {
              plugin.breathe.generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = true, ctx)(p.pos, p.info, NodeTrafo(p))
            }
          } else {
            Seq(Assert(BoolLit(b = false)())())
          }
        case _ => Seq()
      }) ++
        Seq[Stmt](ctx.noRec(p)) ++
        plugin.breathe.splitBreathing(p.wand.left, Some(true), {
          case accessPredicate: AccessPredicate if !plugin.isAccIgnored(accessPredicate.loc) =>
            val normalized = plugin.normalize.normalizeExpression(accessPredicate.perm, plugin.normalize.rdPermContext)
            if (normalized.isDefined) {
              if (normalized.get.wildcard.isDefined) {
                plugin.reportError(Internal(p, FeatureUnsupported(p, "Rdc is not allowed in wands")))
                Seq(Assert(BoolLit(b = false)())())
              } else {
                plugin.breathe.generateLogUpdate(input, accessPredicate.loc, normalized.get, minus = false, ctx)(p.pos, p.info, NodeTrafo(p))
              }
            } else {
              Seq(Assert(BoolLit(b = false)())())
            }
          case _ => Seq()
        }),
      Seq()
    )(p.pos, p.info)
  }

}