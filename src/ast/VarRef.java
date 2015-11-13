package ast;

import visitor.Visitor;

public class VarRef implements Node {
    private final String var;

    public VarRef(String var) {
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
