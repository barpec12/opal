/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj
package bi
package reader

import java.io.DataInputStream

/**
 * Generic parser for `RuntimeVisibleParameterAnnotations` attributes.
 */
trait RuntimeVisibleParameterAnnotations_attributeReader extends AttributeReader {

    type ParameterAnnotations
    type ParametersAnnotations <: Traversable[ParameterAnnotations]
    /**
     * Method that delegates to another reader to parse the annotations of the parameters.
     */
    def ParametersAnnotations(cp: Constant_Pool, in: DataInputStream): ParametersAnnotations

    type RuntimeVisibleParameterAnnotations_attribute >: Null <: Attribute

    def RuntimeVisibleParameterAnnotations_attribute(
        constant_pool:         Constant_Pool,
        attribute_name_index:  Constant_Pool_Index,
        parameter_annotations: ParametersAnnotations
    ): RuntimeVisibleParameterAnnotations_attribute

    //
    // IMPLEMENTATION
    //

    /**
     * <pre>
     * RuntimeVisibleParameterAnnotations_attribute {
     *  u2 attribute_name_index;
     *  u4 attribute_length;
     *  u1 num_parameters;
     *  {
     *      u2 num_annotations;
     *      annotation annotations[num_annotations];
     *      } parameter_annotations[num_parameters];
     *  }
     * </pre>
     */
    private[this] def parserFactory() = (
        ap: AttributeParent,
        cp: Constant_Pool,
        attribute_name_index: Constant_Pool_Index,
        in: DataInputStream
    ) ⇒ {
        /*val attribute_length =*/ in.readInt()
        val parameter_annotations = ParametersAnnotations(cp, in)
        if (parameter_annotations.nonEmpty || reifyEmptyAttributes) {
            RuntimeVisibleParameterAnnotations_attribute(
                cp, attribute_name_index, parameter_annotations
            )
        } else {
            null
        }
    }

    registerAttributeReader(RuntimeVisibleParameterAnnotationsAttribute.Name → parserFactory())

}
