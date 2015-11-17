package tool;

import ast.AssertStmt;

import java.util.Map;

public class SMTModel {
    private final Map<Integer, AssertStmt> indexToAssert;
    private final String code;

    public SMTModel(Map<Integer, AssertStmt> indexToAsserts, String code) {
        this.code = code;
        this.indexToAssert = indexToAsserts;
    }

    public Map<Integer, AssertStmt> getIndexToAssert() {
        return indexToAssert;
    }

    public String getCode() {
        return code;
    }
}
