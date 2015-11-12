package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class VarRefExpr implements AtomExpr {
    private final VarRef varRef;

    public VarRefExpr(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(varRef);
    }
}
