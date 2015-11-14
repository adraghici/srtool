package ast;

import visitor.Visitor;

public class MethodRef implements Node {
    private final String var;

    public MethodRef(String var) {
        this.var = var;
    }

    public String getVar() {
        return var;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
