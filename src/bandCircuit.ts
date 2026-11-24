import type { CircuitInput } from './circuit.js'
import type { IntervalMath } from './interval.js'

export interface DistributedPortIntervals<T> {
  mass: T
  response(frequency: T): { throatFlow: T; reactance: T; peak(): T }
}

/** Enclose the cleared circuit equations in circuit.ts per terminal RMS volt. */
export function bandCircuit<T>(input: CircuitInput, math: IntervalMath<T>, measureMach: boolean,
  distributed?: DistributedPortIntervals<T>) {
  const { exact, minus, one, pi, plus, quotient, root, square, times, zero } = math
  type Phasor = { re: T; im: T }
  const real = (re: T): Phasor => ({ re, im: zero })
  const add = (a: Phasor, b: Phasor): Phasor =>
    ({ re: plus(a.re, b.re), im: plus(a.im, b.im) })
  const mul = (a: Phasor, b: Phasor): Phasor => ({
    re: minus(times(a.re, b.re), times(a.im, b.im)),
    im: plus(times(a.re, b.im), times(a.im, b.re)),
  })
  const magnitude = (a: Phasor) => root(plus(square(a.re), square(a.im)))
  const tau = times(exact(2), pi)
  const peak = root(exact(2))
  const { driver, medium, port, passiveRadiator: radiator } = input
  const count = exact(input.quantity ?? 1)
  const series = exact(input.seriesDrivers ?? 1)
  const parallel = quotient(count, series)
  const rho = exact(medium.densityKgM3)
  const speed = exact(medium.soundSpeedMps)
  const rhoC2 = times(rho, square(speed))
  const cab = quotient(exact(input.volumeM3), rhoC2)
  const area = square(exact(driver.sdM2))
  const compliance = quotient(exact(driver.vasM3), times(rhoC2, area))
  const fs = times(tau, exact(driver.fsHz))
  const mass = quotient(one, times(square(fs), compliance))
  const resistance = quotient(times(fs, mass), exact(driver.qms))
  const re = exact(driver.reOhms)
  const bl2 = quotient(times(times(fs, mass), re), exact(driver.qes))
  const motorDrive = quotient(root(bl2), series)
  const coneArea = times(count, exact(driver.sdM2))
  const coupling = times(count, area)

  const portMass = distributed?.mass ??
    (port ? quotient(times(rho, exact(port.effectiveLengthM!)), exact(port.areaM2!)) : zero)
  const radiatorArea = radiator ? times(exact(radiator.quantity ?? 1), exact(radiator.sdM2)) : zero
  const radiatorAreaTerm = radiator ? times(radiatorArea, exact(radiator.sdM2)) : zero
  const characteristic = port ? root(quotient(portMass, cab))
    : radiator ? root(quotient(exact(radiator.movingMassKg), times(radiatorAreaTerm, cab)))
    : quotient(one, times(times(fs, cab), root(plus(one,
      quotient(times(exact(driver.vasM3), count), exact(input.volumeM3))))))
  const portResistance = port && port.quality !== Infinity
    ? quotient(quotient(portMass, root(times(portMass, cab))), exact(port.quality)) : zero
  const loss = (quality: number) => quality === Infinity ? zero : quotient(one, times(exact(quality), characteristic))
  const conductance = plus(loss(input.leakageQuality), loss(input.absorptionQuality))

  return (frequency: T) => {
    const omega = times(tau, frequency)
    const duct = distributed?.response(frequency)
    const portReactance = times(omega, portMass)
    const portNorm = plus(square(portResistance), square(portReactance))
    const yPort = duct ? real(duct.throatFlow) : port ? {
      re: quotient(portResistance, portNorm),
      im: quotient(minus(zero, portReactance), portNorm),
    } : real(zero)
    const base = { re: conductance, im: times(omega, cab) }
    const branch = duct ? { re: times(portResistance, duct.throatFlow), im: duct.reactance } : radiator ? {
      re: exact(radiator.mechanicalResistanceNsPerM),
      im: minus(times(omega, exact(radiator.movingMassKg)),
        quotient(one, times(omega, exact(radiator.complianceMPerN)))),
    } : real(one)
    const admittance = duct ? add(mul(base, branch), yPort)
      : radiator ? add(mul(base, branch), real(radiatorAreaTerm)) : add(base, yPort)
    const mech = add(mul({
      re: resistance, im: minus(times(omega, mass), quotient(one, times(omega, compliance))),
    }, admittance), mul(real(coupling), branch))
    const denominator = magnitude(add(
      mul({ re, im: times(omega, exact(driver.leHenries)) }, mech),
      mul(real(bl2), admittance),
    ))
    const coneVelocity = quotient(times(motorDrive, magnitude(admittance)), denominator)
    // The same throat-flow factor occurs in branch admittance and in the
    // throat-to-mouth ratio. Cancel it before evaluating the interior speed.
    const portSpeedFactor = !measureMach ? zero : duct ? duct.peak()
      : port ? quotient(magnitude(yPort), exact(port.areaM2!)) : zero
    return {
      excursion: quotient(times(peak, coneVelocity), omega),
      current: quotient(times(quotient(parallel, series), magnitude(mech)), denominator),
      portMach: quotient(times(times(times(peak, motorDrive), coneArea), portSpeedFactor),
        times(denominator, speed)),
      radiatorExcursion: radiator ? quotient(times(times(times(peak, motorDrive), coneArea), radiatorAreaTerm),
        times(times(denominator, omega), radiatorArea)) : zero,
    }
  }
}
