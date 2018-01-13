package viper.silver.plugin

import java.io.InputStream
import java.nio.file.{Files, Path, Paths}

import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, TranslatorState}
import viper.silver.verifier.{Failure, Success, Verifier}

import scala.io.Source

/** Minimal SilFrontend to load a file and translate it into an AST
  * Will probably break if it is used for something else than loadFile.
  */
class ARPFrontend(plugin: ARPPlugin) extends SilFrontend{

  override def createVerifier(fullCmd: String): Verifier =
    sys.error("Implementation missing")

  override def configureVerifier(args: Seq[String]): SilFrontendConfig =
    sys.error("Implementation missing")

  def loadFile(name: String, stream: InputStream): Option[Program] ={
    _plugins = SilverPluginManager(None)
    _state = TranslatorState.Initialized
    myReset(name, stream)
    plugin.performance.start()
    translate()
    plugin.performance.stop("loadFile translate")

    if (_errors.nonEmpty) {
      logger.info(s"Could not load $name:")
      _errors.foreach(e => logger.info(s"  ${e.readableMessage}"))
    }
    _program
  }

  def myReset(input: String, stream: InputStream): Unit = {
    if (state < TranslatorState.Initialized) sys.error("The translator has not been initialized.")
    _state = TranslatorState.InputSet
    _inputFile = Some(Paths.get(input))
    _input = Some(Source.fromInputStream(stream).mkString)
    _errors = Seq()
    _program = None
    _verificationResult = None
    _parseResult = None
    _typecheckResult = None
    resetMessages()
  }
}
