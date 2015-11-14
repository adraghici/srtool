package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Map;

public class OldExpr implements AtomExpr {
    private List<Node> children;

    public OldExpr(VarRef varRef) {
        this.children = Lists.newArrayList(varRef);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    public List<Node> getChildren() {
        return children;
    }

    @Override
    public void setChildren(List<Node> children) {
        this.children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> vars) {
        return this;
    }
}
