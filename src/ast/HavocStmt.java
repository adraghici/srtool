package ast;

import com.google.common.collect.Sets;

import java.util.Set;

public class HavocStmt implements Stmt {
    private final VarRef varRef;

    public HavocStmt(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public Set<String> getModified() {
        return Sets.newHashSet(varRef.getVar());
    }
}
