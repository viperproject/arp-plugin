/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silicon

package object common {
  trait Mergeable[S <: Mergeable[S]] {
    def merge(other: S): S
  }
}
