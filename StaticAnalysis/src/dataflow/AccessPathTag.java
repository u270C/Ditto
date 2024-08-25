package dataflow;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

/**
 * @program: Ditto
 * @description:
 **/ //An access path length of 0 indicates that the current variable is a pollution. The current variable can be a local variable, this, an instance field, or a static field
//A taint, if its access path is 0, indicates that the object to which the reference refers is contaminated
//If the access path is not 0, it means that the object to which the reference refers is contaminated. For example, if the reference is taint and the access path is.x.y.z, then taint.x.y.z is contaminated
public class AccessPathTag implements Tag {

    private int fieldLength = 0;

    private String fieldChain = "";
    int accessPathIndex=0;

    @Override
    public String getName() {
        return "AccessPath";
    }

    public AccessPathTag(Tag tag) {
        AccessPathTag accessPathTag = (AccessPathTag) tag;
        fieldChain = accessPathTag.fieldChain;
        fieldLength=accessPathTag.fieldLength;
    }

    public AccessPathTag() {

    }


    @Override
    public byte[] getValue() throws AttributeValueException {
        return null;
    }

    public boolean appendAccessPath(String fieldName) {
        if (fieldLength == 5) {
            return false;
        } else {
            fieldChain = fieldName + "." + fieldChain;
            fieldLength += 1;
            return true;
        }
    }

    public boolean removeAccessPath() {
        if (fieldLength == 0)
            return true;
        byte[] bytes = fieldChain.getBytes();
        for (int i = 0; i < fieldChain.length(); i++) {
            if ((char) bytes[i] == '.') {
                fieldChain = fieldChain.substring(i+1);
                return true;
            }
        }
        return false;

    }

    public void setValue(byte[] value) {
    }

    public boolean match(String fieldName) {
        if (fieldChain.isEmpty())
            return true;
        String[] split = fieldChain.split("/.");
        return split[0].replace(".","").equals(fieldName);
    }

    public int getFieldLength() {
        return fieldLength;
    }

    public String getFieldChain(){
        return fieldChain;
    }
}
