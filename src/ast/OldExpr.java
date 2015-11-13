package ast;

import visitor.Visitor;

public class OldExpr implements AtomExpr {
    private final VarRef varRef;

    public OldExpr(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
