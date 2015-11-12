package ast;

import com.google.common.collect.Lists;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class ProcedureDecl implements Node {
    private final String name;
    private final List<VarRef> params;
    private final List<PrePostCondition> conditions;
    private final List<Stmt> stmts;
    private final Expr returnExpr;

    public ProcedureDecl(String name, List<VarRef> params, List<PrePostCondition> conditions,
        List<Stmt> stmts, Expr returnExpr) {
        this.name = name;
        this.params = params;
        this.conditions = conditions;
        this.stmts = stmts;
        this.returnExpr = returnExpr;
    }

    public String getName() {
        return name;
    }

    public List<VarRef> getParams() {
        return params;
    }

    public List<PrePostCondition> getConditions() {
        return conditions;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    public Expr getReturnExpr() {
        return returnExpr;
    }

    @Override
    public Set<String> getModset() {
        return stmts.stream().map(Stmt::getModset).flatMap(Set::stream).collect(Collectors.toSet());
    }

    @Override
    public List<Node> getChildren() {
        ArrayList<Node> children = Lists.newArrayList(conditions);
        children.addAll(stmts);
        return children;
    }
}
