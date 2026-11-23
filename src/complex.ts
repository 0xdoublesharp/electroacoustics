/** RMS phasors, exp(j omega t). */
export interface Complex {
  re: number
  im: number
}
export const c = (re: number, im = 0): Complex => ({ re, im })
export const add = (a: Complex, b: Complex): Complex =>
  c(a.re + b.re, a.im + b.im)
export const sub = (a: Complex, b: Complex): Complex =>
  c(a.re - b.re, a.im - b.im)
export const mul = (a: Complex, b: Complex): Complex =>
  c(a.re * b.re - a.im * b.im, a.im * b.re + a.re * b.im)
export function div(a: Complex, b: Complex): Complex {
  const d = b.re * b.re + b.im * b.im
  return c((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d)
}
export const reciprocal = (a: Complex): Complex => div(c(1), a)
export const magnitude = (a: Complex): number => Math.hypot(a.re, a.im)
