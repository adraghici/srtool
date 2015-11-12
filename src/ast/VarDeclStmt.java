package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class VarDeclStmt implements Stmt {
    private final VarRef varRef;

    public VarDeclStmt(VarRef varRef) {
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
