/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.plugin

class ARPPerformance {

  var timers: Seq[Long] = Seq[Long]()

  lazy val printEnabled = System.getProperty("DEBUGPERF", "").equals("1")

  def start(): Unit ={
    timers +:= System.currentTimeMillis()
  }

  def stop(name: String): Long ={
    val now = System.currentTimeMillis()
    val time = now - timers.head
    timers = timers.tail
    if (printEnabled && name.nonEmpty) {
      println(" " * timers.size * 2 + name + " finished in " + time / 1000.0 + " seconds")
    }
    time
  }

  def measure[T](name: String)(something: => T): T = {
    start()
    val result = something
    stop(name)
    result
  }

}
