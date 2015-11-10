package ast;

import com.google.common.collect.Lists;

import java.util.ArrayList;
import java.util.List;

public class ProcedureDecl implements Node {
    private final String name;
    private final List<String> params;
    private final List<PrePostCondition> conditions;
    private final List<Stmt> stmts;
    private final Expr returnExpr;

    public ProcedureDecl(String name, List<String> params, List<PrePostCondition> conditions,
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

    public List<String> getParams() {
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
    public List<Node> getChildren() {
        ArrayList<Node> children = Lists.newArrayList(conditions);
        children.addAll(stmts);
        return children;
    }
}
