/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.js

import org.opalj.tac.fpcf.analyses.ifds.taint.Fact

/* Common trait for facts for ScriptEngines. */
trait JSFact extends Fact

/**
 * A tainted value inside a Key-Value-Map
 *
 * @param index map
 * @param keyName name of the key. Empty string if unknown.
 */
case class BindingFact(index: Int, keyName: String) extends JSFact
