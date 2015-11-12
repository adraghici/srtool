package ast;

import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class AssignStmt implements Stmt {
    private final VarRef varRef;
    private final Expr expr;

    public AssignStmt(VarRef varRef, Expr expr) {
        this.varRef = varRef;
        this.expr = expr;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet(varRef.getVar());
    }

    @Override
    public List<Node> getChildren() {
        return null;
    }
}
