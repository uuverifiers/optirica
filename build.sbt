name := "OptiRica";
organization := "uuverifiers";
version := "0.1";
homepage := Some(url("https://github.com/uuverifiers/optirica"));
licenses := Seq("BSD License 2.0" -> url("https://github.com/uuverifiers/optirica/blob/master/LICENSE"));

scalaVersion := "2.11.12";

resolvers += ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven/").withAllowInsecureProtocol(true);

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.14.0" % "test";

libraryDependencies += "uuverifiers" %% "eldarica" % "nightly-SNAPSHOT";
