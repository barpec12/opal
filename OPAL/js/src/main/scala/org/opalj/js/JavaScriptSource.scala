/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import java.io.{File, FileOutputStream}
import java.nio.file.Files
sealed trait JavaScriptSource {
    def asString: String
    def asFile(codeBefore: String, codeAfter: String): File
}

case class JavaScriptStringSource(source: String) extends JavaScriptSource {
    lazy val tmpFile: File = Files.createTempFile("opal", ".js").toFile

    override def asString: String = source

    override def asFile(codeBefore: String, codeAfter: String): File = {
        val code = codeBefore + source + codeAfter;
        val fos = new FileOutputStream(tmpFile);
        fos.write(code.getBytes())
        fos.close()
        tmpFile
    }
}

case class JavaScriptFileSource(path: String) extends JavaScriptSource {
    override def asString: String = path

    override def asFile(codeBefore: String, codeAfter: String): File = null;
}
