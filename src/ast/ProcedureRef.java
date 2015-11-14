package ast;

import visitor.Visitor;

public class ProcedureRef implements Node {
    private final String var;

    public ProcedureRef(String var) {
        this.var = var;
    }

    public String getName() {
        return var;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
