/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import java.io.File
import java.nio.file.Files

trait JavaScriptSource {
    def asString: String
    def asFile: File
}

case class JavaScriptStringSource(source: String) extends JavaScriptSource {
    lazy val tmpFile: File = Files.createTempFile("opal", ".js").toFile;

    override def asString: String = source

    override def asFile: File = tmpFile
}

case class JavaScriptFileSource(path: String) extends JavaScriptSource {
    override def asString: String = path

    override def asFile: File = null;
}
