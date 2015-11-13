package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Set;

public class AssignStmt implements Stmt {
    private List<Node> children;

    public AssignStmt(VarRef varRef, Expr expr) {
        this.children = Lists.newArrayList(varRef, expr);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    public Expr getExpr() {
        return (Expr) children.get(1);
    }

    @Override
    public Set<String> getModified() {
        return Sets.newHashSet(getVarRef().getVar());
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
