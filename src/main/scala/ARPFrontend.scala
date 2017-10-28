package viper.silver.plugin

import java.nio.file.Path

import viper.silver.ast.Program
import viper.silver.frontend.{SilFrontend, SilFrontendConfig, TranslatorState}
import viper.silver.verifier.{Failure, Success, Verifier}

/** Minimal SilFrontend to load a file and translate it into an AST
  * Will probably break if it is used for something else than loadFile.
  */
class ARPFrontend extends SilFrontend{

  override def createVerifier(fullCmd: String): Verifier =
    sys.error("Implementation missing")

  override def configureVerifier(args: Seq[String]): SilFrontendConfig =
    sys.error("Implementation missing")

  def loadFile(path: Path): Option[Program] ={
    _plugins = SilverPluginManager(None)
    _state = TranslatorState.Initialized
    reset(path)
    translate()

    if (_errors.nonEmpty) {
      logger.info(s"Could not load ${path.getFileName}:")
      _errors.foreach(e => logger.info(s"  ${e.readableMessage}"))
    }
    _program
  }
}
