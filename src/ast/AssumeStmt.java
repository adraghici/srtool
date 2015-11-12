package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class AssumeStmt implements Condition, Stmt {
    private final Expr condition;

    public AssumeStmt(Expr condition) {
        this.condition = condition;
    }

    @Override
    public Expr getCondition() {
        return condition;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(condition);
    }
}
