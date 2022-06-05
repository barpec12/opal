/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import java.io.File

trait JavaScriptSource {
    def asString: String
    def asFile: File
}

case class JavaScriptStringSource(source: String) extends JavaScriptSource {
    override def asString: String = source

    // TODO: create new temp file
    override def asFile: File = null
}

case class JavaScriptFileSource(path: String) extends JavaScriptSource {
    override def asString: String = ""

    override def asFile: File = null
}
