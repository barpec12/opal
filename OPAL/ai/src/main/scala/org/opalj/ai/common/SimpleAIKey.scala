/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj
package ai
package common

import scala.collection.concurrent.TrieMap

import org.opalj.br.Method
import org.opalj.br.analyses.ProjectInformationKey
import org.opalj.br.analyses.SomeProject
import org.opalj.ai.domain.RecordDefUse
import org.opalj.ai.domain.l1.DefaultDomainWithCFGAndDefUse

/**
 * Key to get the result of the abstract interpretation of a method using a configured domain
 * factory. The factory is configured using project specific configuration data.
 *
 * @example To specify the domain that you want to use for performing the abstract interpretation:
 * {{{
 *  project.getOrCreateProjectInformationKeyInitializationData(
 *      SimpleAIKey,
 *      (m: Method) ⇒ {
 *          // call the constructor of the domain of your liking
 *          new org....Domain(p,m)
 *      }
 *  )
 * }}}
 *
 * @note   To get the index use the [[org.opalj.br.analyses.Project]]'s `get` method and
 *         pass in `this` object.
 *
 * @author Michael Eichberg
 */
object SimpleAIKey extends AIKey {

    /**
     * The SimpleAIKey has no special prerequisites.
     */
    override protected def requirements: Seq[ProjectInformationKey[Nothing, Nothing]] = Nil

    /**
     * Returns an object which performs and caches the result of the abstract interpretation of a
     * method when required.
     *
     * All methods belonging to a project are analyzed using the same `domainFactory`. Hence,
     * the `domainFactory` needs to be set before compute is called/this key is passed to a
     * specific project. If multiple projects are instead concurrently, external synchronization
     * is necessary (e.g., on the ProjectInformationKey) to ensure that each project is
     * instantiated using the desired domain.
     */
    override protected def compute(
        project: SomeProject
    ): Method ⇒ AIResult { val domain: Domain with RecordDefUse } = {

        val domainFactory = project.
            getProjectInformationKeyInitializationData(this).
            getOrElse((m: Method) ⇒ new DefaultDomainWithCFGAndDefUse(project, m))

        val aiResults = TrieMap.empty[Method, AIResult { val domain: Domain with RecordDefUse }]

        (m: Method) ⇒ {
            aiResults.get(m) match {
                case Some(taCode) ⇒ taCode
                case None ⇒
                    val brCode = m.body.get
                    // Basically, we use double checked locking; we really don't want to
                    // transform the code more than once!
                    brCode.synchronized {
                        aiResults.get(m) match {
                            case Some(aiResult) ⇒ aiResult
                            case None ⇒
                                val aiResult = BaseAI(m, domainFactory(m))
                                aiResults.put(m, aiResult)
                                aiResult
                        }
                    }
            }
        }
    }
}
