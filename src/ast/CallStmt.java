package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class CallStmt implements Stmt {
    private List<Node> children;

    public CallStmt(VarRef varRef, MethodRef methodRef, List<Expr> args) {
        children = Lists.newArrayList(varRef, methodRef);
        children.addAll(args);
    }

    public VarRef getVarRef() {
        return (VarRef) children.get(0);
    }

    public MethodRef getMethodRef() {
        return (MethodRef) children.get(1);
    }

    public List<Expr> getArgs() {
        return children.stream()
            .filter(x -> x instanceof Expr)
            .map(x -> (Expr) x)
            .collect(Collectors.toList());
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
    public void setChildren(List<Node> children) {
        this.children = Lists.newArrayList(children);
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
