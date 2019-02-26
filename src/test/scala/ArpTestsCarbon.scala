// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.
/*
package viper.carbon

import java.nio.file.Path

import viper.silver.frontend.Frontend
import viper.silver.reporter.{NoopReporter, Reporter, StdIOReporter}
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier

/** All tests for carbon.

  */
class ArpTestsCarbon extends SilSuite {
  private val arpTestDirectories = Seq("arp")
  private val silTestDirectories = Seq("all", "quantifiedpermissions", "wands", "examples", "quantifiedpredicates" ,"quantifiedcombinations")
  //  val testDirectories = arpTestDirectories
  val testDirectories = arpTestDirectories ++ silTestDirectories
  //, "generated"

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new MyCarbonFrontend(new StdIOReporter("carbon_for_testing"))
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  lazy val verifiers = List(createCarbonInstance())

  val commandLineArguments: Seq[String] = Seq("--plugin", "ARPPlugin")

  private def createCarbonInstance() = {
    val args = commandLineArguments
    val debugInfo = ("startedBy" -> "viper.carbon.ARPTestsCarbon") :: Nil
    val carbon = CarbonVerifier(debugInfo)
    carbon.parseCommandLine(args :+ "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver")

    carbon
  }

  class MyCarbonFrontend(override val reporter: Reporter) extends CarbonFrontend(reporter) {
    override def init(verifier: Verifier): Unit = {
      super.init(verifier)

      _config = verifier.asInstanceOf[CarbonVerifier].config
    }
  }
}
*/
