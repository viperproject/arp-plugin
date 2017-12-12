///*
// * This Source Code Form is subject to the terms of the Mozilla Public
// * License, v. 2.0. If a copy of the MPL was not distributed with this
// * file, You can obtain one at http://mozilla.org/MPL/2.0/.
// */
//
//package viper.carbon
//
//import java.nio.file.Path
//
//import viper.silver.frontend.Frontend
//import viper.silver.reporter.StdIOReporter
//import viper.silver.testing.SilSuite
//import viper.silver.verifier.Verifier
//
///** All tests for carbon.
//
//  */
//class ArpTestsCarbon extends SilSuite {
//  private val arpTestDirectories = Seq("arp")
//  private val siliconTestDirectories = Seq("consistency")
//  private val silTestDirectories = Seq("all", "quantifiedpermissions", "wands", "examples", "quantifiedpredicates" ,"quantifiedcombinations")
//  //  val testDirectories = arpTestDirectories
//  //  val testDirectories = siliconTestDirectories ++ silTestDirectories
//  val testDirectories = arpTestDirectories ++ siliconTestDirectories ++ silTestDirectories
//    //, "generated"
//
//  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
//    require(files.length == 1, "tests should consist of exactly one file")
//    val fe = new CarbonFrontend(new StdIOReporter("carbon_for_testing"))
//    fe.init(verifier)
//    fe.reset(files.head)
//    fe
//  }
//
//  lazy val verifiers = List(CarbonVerifier())
//}
