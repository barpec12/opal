package org.opalj.fpcf.fixtures.js;

import org.opalj.fpcf.properties.taint.ForwardFlowPath;

import javax.script.Invocable;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import static java.lang.Integer.parseInt;

public class Java2JsTestClass {
    private static int staticField;

    private int instanceField;

    @ForwardFlowPath({"simpleScriptEngine"})
    public static void simpleScriptEngine() throws ScriptException
    {
        ScriptEngineManager sem = new ScriptEngineManager();
        ScriptEngine se = sem.getEngineByName("JavaScript");
        int x = parseInt("1337");
        try {
            if (x == 0) {
                se.eval("function check(str) {\n" +
                        "    return str === \"1337\";\n" +
                        "}");
            } else {
                se.eval("function check(str) {\n" +
                        "    return str === \"42\";\n" +
                        "}");
            }
        } catch (ScriptException e) {
            // never happens
        }
        String pw = source();

        Invocable inv = (Invocable) se;
        try {
            Boolean state = (Boolean) inv.invokeFunction("check", pw);
            sink(state);
        } catch (NoSuchMethodException e) {
            // never happens
        }
    }

    public static String source() {
        return "1337";
    }

    private static int sanitize(int i) {return i;}

    private static void sink(int i) {
        System.out.println(i);
    }
    private static void sink(String i) {
        System.out.println(i);
    }
    private static void sink(boolean i) {
        System.out.println(i);
    }
}
