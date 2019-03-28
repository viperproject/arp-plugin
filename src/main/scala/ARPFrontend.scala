// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import java.io.InputStream
import java.nio.file.Paths

import viper.silver.ast.Program
import viper.silver.frontend.{DefaultStates, SilFrontend, SilFrontendConfig}
import viper.silver.verifier.Verifier

import scala.io.Source

/** Minimal SilFrontend to load a file and translate it into an AST
  * Will probably break if it is used for something else than loadFile.
  */
class ARPFrontend(plugin: ARPPlugin) extends SilFrontend{

  override def createVerifier(fullCmd: String): Verifier =
    sys.error("Implementation missing")

  override def configureVerifier(args: Seq[String]): SilFrontendConfig =
    sys.error("Implementation missing")

  def loadFile(name: String, stream: InputStream): Option[Program] = {
    val oldState = _state
    _plugins = SilverPluginManager()
    _state = DefaultStates.Initialized
    myReset(name, stream)
    plugin.performance.start()
    parsing()
    semanticAnalysis()
    translation()
    plugin.performance.stop("loadFile translate")

    if (_errors.nonEmpty) {
      logger.info(s"Could not load $name:")
      _errors.foreach(e => logger.info(s"  ${e.readableMessage}"))
    }
    _state = oldState
    _program
  }

  def myReset(input: String, stream: InputStream): Unit = {
    if (state < DefaultStates.Initialized) sys.error("The translator has not been initialized.")
    _state = DefaultStates.InputSet
    _inputFile = Some(Paths.get(input))
    _input = Some(Source.fromInputStream(stream).mkString)
    _errors = Seq()
    _program = None
    _verificationResult = None
    _parsingResult = None
    _semanticAnalysisResult = None
    resetMessages()
  }
}
