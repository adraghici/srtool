package ast;

import visitor.Visitor;

import java.util.Map;

public class VarRefExpr implements AtomExpr {
    private final VarRef varRef;

    public VarRefExpr(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> substitutes) {
        if (substitutes.containsKey(getVarRef().getVar())) {
            return substitutes.get(getVarRef().getVar());
        }
        return this;
    }
}
