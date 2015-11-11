package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class HavocStmt implements Stmt {
    private final VarRef varRef;

    public HavocStmt(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
