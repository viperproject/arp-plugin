/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */
/*
package viper.silicon.tests

import java.nio.file.Path

import viper.silicon.{Silicon, SiliconFrontend, SymbExLogger}
import viper.silver.plugin.SilverPluginManager
import viper.silver.reporter.NoopReporter
import viper.silver.testing.{LocatedAnnotation, MissingOutput, SilSuite, UnexpectedOutput}
import viper.silver.verifier.{Verifier, Failure => SilFailure, Success => SilSuccess, VerificationResult => SilVerificationResult}

class ArpTests extends SilSuite {
  private val arpTestDirectories = Seq("arp")
  private val siliconTestDirectories = Seq("consistency")
  private val silTestDirectories = Seq("all", "quantifiedpermissions", "wands", "examples", "quantifiedpredicates" ,"quantifiedcombinations")
  val testDirectories = arpTestDirectories
//  val testDirectories = siliconTestDirectories ++ silTestDirectories
//  val testDirectories = arpTestDirectories ++ siliconTestDirectories ++ silTestDirectories

  override def frontend(verifier: Verifier, files: Seq[Path]) = {
    require(files.length == 1, "tests should consist of exactly one file")

    // For Unit-Testing of the Symbolic Execution Logging, the name of the file
    // to be tested must be known, which is why it's passed here to the SymbExLogger-Object.
    // SymbExLogger.reset() cleans the logging object (only relevant for verifying multiple
    // tests at once, e.g. with the 'test'-sbt-command.
    SymbExLogger.reset()
    SymbExLogger.filePath = files.head
    SymbExLogger.initUnitTestEngine()
    val fe = new SiliconFrontend(NoopReporter)//SiliconFrontendWithUnitTesting()
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def annotationShouldLeadToTestCancel(ann: LocatedAnnotation) = {
    ann match {
      case UnexpectedOutput(_, _, _, _, _, _) => true
      case MissingOutput(_, _, _, _, _, issue) => issue != 34
      case _ => false
    }
  }

  lazy val verifiers = List(createSiliconInstance())

  val commandLineArguments: Seq[String] = Seq("--plugin", "viper.silver.plugin.ARPPlugin")

  private def createSiliconInstance() = {
    val args =
      commandLineArguments ++
      Silicon.optionsFromScalaTestConfigMap(prefixSpecificConfigMap.getOrElse("silicon", Map()))
    val reporter = NoopReporter
    val debugInfo = ("startedBy" -> "viper.silicon.ARPTests") :: Nil
    val silicon = Silicon.fromPartialCommandLineArguments(args, reporter, debugInfo)

    silicon
  }
}

class SiliconFrontendWithUnitTesting extends SiliconFrontend(NoopReporter) {

  // patch missing plugin
  override def init(verifier: Verifier): Unit = {
    super.init(verifier)
    _plugins = SilverPluginManager(_config.plugin.toOption)
  }
}
*/
