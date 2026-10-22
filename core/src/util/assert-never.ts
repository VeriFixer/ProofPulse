/** Compile-time exhaustiveness check for switch statements over enums. */
export function assertNever(value: never, what = "value"): never {
  throw new Error(`Unexpected ${what}: ${String(value)}`);
}
