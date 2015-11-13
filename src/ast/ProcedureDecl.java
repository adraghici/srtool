package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class ProcedureDecl implements Node {
    private final String name;
    private List<Node> children;

    public ProcedureDecl(String name, List<VarRef> params, List<PrePostCondition> conditions,
        List<Stmt> stmts, Expr returnExpr) {
        this.name = name;
        this.children = Lists.newArrayList(params);
        this.children.addAll(conditions);
        this.children.addAll(stmts);
        this.children.add(returnExpr);
    }

    public String getName() {
        return name;
    }

    public List<VarRef> getParams() {
        return children.stream()
            .filter(x -> x instanceof VarRef)
            .map(x -> (VarRef) x)
            .collect(Collectors.toList());
    }

    public List<PrePostCondition> getConditions() {
        return children.stream()
            .filter(x -> x instanceof PrePostCondition)
            .map(x -> (PrePostCondition) x)
            .collect(Collectors.toList());
    }

    public List<Stmt> getStmts() {
        return children.stream()
            .filter(x -> x instanceof Stmt)
            .map(x -> (Stmt) x)
            .collect(Collectors.toList());
    }

    public Expr getReturnExpr() {
        return children.stream()
            .filter(x -> x instanceof Expr)
            .map(x -> (Expr) x)
            .collect(Collectors.toList()).get(0);
    }

    @Override
    public Set<String> getModified() {
        return getStmts().stream()
            .map(Stmt::getModified)
            .flatMap(Set::stream)
            .collect(Collectors.toSet());
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
