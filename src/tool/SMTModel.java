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

    public AssertStmt getAssert(int id) {
        return indexToAssert.get(id);
    }

    public String getCode() {
        return code;
    }
}
