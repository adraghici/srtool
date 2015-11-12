package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class VarDeclStmt implements Stmt {
    private final VarRef varRef;

    public VarDeclStmt(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet(varRef.getVar());
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
