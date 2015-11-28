package visitor;

import ast.AssertStmt;
import ast.AssumeStmt;
import ast.NumberExpr;

public class ValuesRangeVisitor extends DefaultVisitor {
    private int min;
    private int max;
    private boolean inAssumeOrAssert;

    public ValuesRangeVisitor() {
        min = Integer.MAX_VALUE;
        max = Integer.MIN_VALUE;
        inAssumeOrAssert = false;
    }

    @Override
    public Void visit(AssertStmt assertStmt) {
        inAssumeOrAssert = true;
        assertStmt.getCondition().accept(this);
        inAssumeOrAssert = false;
        return null;
    }

    @Override
    public Void visit(AssumeStmt assumeStmt) {
        inAssumeOrAssert = true;
        assumeStmt.getCondition().accept(this);
        inAssumeOrAssert = false;
        return null;
    }

    @Override
    public Void visit(NumberExpr numberExpr) {
        if (!inAssumeOrAssert) {
            return null;
        }

        int number = Integer.valueOf(numberExpr.getNumber());

        if (number < min) {
            min = number;
        }
        if (number > max) {
            max = number;
        }
        return null;
    }

    public int getMinValue() {
        return min;
    }

    public int getMaxValue() {
        return max;
    }
}
