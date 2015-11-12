package ast;

public class OldExpr implements AtomExpr {
    private final VarRef varRef;

    public OldExpr(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }
}
