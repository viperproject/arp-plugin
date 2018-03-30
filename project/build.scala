import sbt._
import Keys._
import sbtassembly.AssemblyPlugin.autoImport._
import de.oakgrove.SbtBrand.{BrandKeys, brandSettings, Val}
import de.oakgrove.SbtHgId.{HgIdKeys, hgIdSettings}
import com.typesafe.sbt.packager.archetypes.JavaAppPackaging

object ARPBuild extends Build {

  /* Base settings */

  lazy val baseSettings = (
       hgIdSettings
    ++ brandSettings
    ++ Seq(
          organization := "viper",
          version := "1.0-SNAPSHOT",
          scalaVersion := "2.11.8",
          scalacOptions in Compile ++= Seq(
            "-deprecation",
            "-unchecked",
            "-feature"
            /*"-Xfatal-warnings"*/),
          resolvers += "Sonatype OSS Snapshots" at "http://oss.sonatype.org/content/repositories/snapshots/",
          traceLevel := 10,
          maxErrors := 6))

  /* Projects */

  lazy val arp = {
    var p = Project(
      id = "arp",
      base = file("."),
      settings = (
           baseSettings
        ++ Seq(
              name := "ARP",
              mainClass in Compile := None,
              mainClass in assembly := None,
              jarName in assembly := "arp-plugin.jar",
              test in assembly := {},
                /* Skip tests before assembling fat jar. Assembling stops if tests fails. */
              // scalacOptions ++= Seq("-Xelide-below", "1000"),
                /* remove elidable method calls such as in SymbExLogger during compiling */
              fork := true,
                /* Fork Silicon when run and tested. Avoids problems with file
                 * handlers on Windows 7 that remain open until Sbt is closed,
                 * which makes it very annoying to work on test files.
                 *
                 * There have been reports about problems with forking. If you
                 * experience strange problems, disable forking and try again.
                 */
               javaOptions in run ++= Seq("-Xss128M", "-Dfile.encoding=UTF-8"),
               javaOptions in Test += "-Xss128M",
               testOptions in Test += Tests.Argument("-oGK"),
                /* Options passed to JVMs forked by test-related Sbt command.
                 * See http://www.scala-sbt.org/0.12.4/docs/Detailed-Topics/Forking.html
                 * In contrast to what the documentation states, it seemed
                 * that neither were the options passed to Sbt's JVM forwarded
                 * to forked JVMs, nor did "javaOptions in (Test,run)"
                 * work for me (Malte, using Sbt 0.12.4).
                 * You can inspect the settings in effect using via
                 * "show javaOptions" on the Sbt console.
                 */
              publishArtifact in Test := true,
              libraryDependencies ++= externalDep,
              BrandKeys.dataPackage := "viper.silver.plugin.arp",
              BrandKeys.dataObject := "brandingData",
              BrandKeys.data += Val("buildDate", new java.text.SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new java.util.Date)),
              BrandKeys.data <+= scalaVersion(Val("scalaVersion", _)),
              BrandKeys.data <+= sbtBinaryVersion(Val("sbtBinaryVersion", _)),
              BrandKeys.data <+= sbtVersion(Val("sbtVersion", _)),
              BrandKeys.data <+= name(Val("sbtProjectName", _)),
              BrandKeys.data <+= version(Val("sbtProjectVersion", _)),
              BrandKeys.data <++= HgIdKeys.projectId(idOrException => {
                val id =
                  idOrException.fold(Predef.identity,
                                     _ => de.oakgrove.SbtHgId.Id("<unknown>", "<unknown>", "<unknown>", "<unknown>"))

                Seq(Val("hgid_version", id.version),
                    Val("hgid_id", id.id),
                    Val("hgid_branch", id.branch),
                    Val("hgid_tags", id.tags))
              }),
              sourceGenerators in Compile <+= BrandKeys.generateDataFile)
        ++ addCommandAlias("tn", "test-only -- -n "))
    )

    for (dep <- internalDep) {
      p = p.dependsOn(dep)
    }

    p.enablePlugins(JavaAppPackaging)
  }

  /* On the build-server, we cannot have all project in the same directory, and
   * thus we use the publish-local mechanism for dependencies.
   */

  def isBuildServer = sys.env.contains("BUILD_TAG") /* Should only be defined on the build server */

  def internalDep = if (isBuildServer) Nil else Seq(
    dependencies.silSrc % "compile->compile;test->test"
  )

  def externalDep = (
    (if (isBuildServer) Seq(dependencies.sil % "compile->compile;test->test") else Nil))

  /* Dependencies */

  object dependencies {
    lazy val sil = "viper" %% "silver" %  "0.1-SNAPSHOT"
    lazy val silSrc = RootProject(new java.io.File("../silver"))
  }
}
