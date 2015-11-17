package ast;

import com.google.common.collect.Sets;
import visitor.Visitor;

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
    public Set<String> getModified() {
        return Sets.newHashSet(getVarRef().getVar());
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
