package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class AssignStmt implements Stmt {
    private final VarRef varRef;
    private final Expr expr;
    private List<Node> children;

    public AssignStmt(VarRef varRef, Expr expr) {
        this.varRef = varRef;
        this.expr = expr;
        this.children = Lists.newArrayList(expr);
    }

    public VarRef getVarRef() {
        return varRef;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public Set<String> getModified() {
        return Sets.newHashSet(varRef.getVar());
    }

    @Override
    public List<Node> getChildren() {
        return children;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
