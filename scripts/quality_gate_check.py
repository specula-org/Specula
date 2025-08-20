#!/usr/bin/env python3
"""
Specula Quality Gate Check Script
Triple-Check Verification System - Gate Enforcement

This script implements automated quality gates for the Specula project,
ensuring enterprise-grade code quality and security standards.
"""

import json
import sys
from pathlib import Path
from typing import Dict
import logging
from datetime import datetime

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


class QualityGateChecker:
    """Quality gate checker for triple-check verification system"""

    def __init__(self, config_path: str = "quality_gate_config.json"):
        self.config = self.load_config(config_path)
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "overall_status": "UNKNOWN",
            "gates": {},
            "summary": {},
        }

    def load_config(self, config_path: str) -> Dict:
        """Load quality gate configuration"""
        try:
            with open(config_path, "r") as f:
                return json.load(f)
        except FileNotFoundError:
            logger.warning(f"Config file {config_path} not found, using defaults")
            return self.get_default_config()

    def get_default_config(self) -> Dict:
        """Get default quality gate configuration"""
        return {
            "sonarqube": {
                "quality_gate": "A",
                "min_score": 85,
                "min_coverage": 90,
                "max_duplications": 3,
                "max_technical_debt": 5,
            },
            "semgrep": {"max_critical": 0, "max_high": 1, "max_medium": 5},
            "bandit": {"max_high": 1, "max_medium": 3, "min_confidence": 80},
            "owasp_zap": {"min_security_score": 90, "max_critical": 0, "max_high": 1},
        }

    def check_sonarqube_quality_gate(self) -> Dict:
        """Check SonarQube quality gate status"""
        logger.info("Checking SonarQube quality gate...")

        try:
            # Check if SonarQube results exist
            sonar_results = Path("sonar-report.json")
            if not sonar_results.exists():
                logger.warning("SonarQube results not found, skipping check")
                return {"status": "SKIPPED", "reason": "Results not found"}

            # Parse SonarQube results
            with open(sonar_results, "r") as f:
                data = json.load(f)

            # Extract metrics
            quality_score = data.get("qualityGate", {}).get("score", 0)
            coverage = data.get("coverage", {}).get("percentage", 0)
            duplications = data.get("duplications", {}).get("percentage", 0)
            technical_debt = data.get("technicalDebt", {}).get("percentage", 0)

            # Check quality gate
            passed = True
            issues = []

            if quality_score < self.config["sonarqube"]["min_score"]:
                passed = False
                issues.append(
                    f"Quality score {quality_score} below threshold {self.config['sonarqube']['min_score']}"
                )

            if coverage < self.config["sonarqube"]["min_coverage"]:
                passed = False
                issues.append(
                    f"Coverage {coverage}% below threshold {self.config['sonarqube']['min_coverage']}%"
                )

            if duplications > self.config["sonarqube"]["max_duplications"]:
                passed = False
                issues.append(
                    f"Duplications {duplications}% above threshold {self.config['sonarqube']['max_duplications']}%"
                )

            if technical_debt > self.config["sonarqube"]["max_technical_debt"]:
                passed = False
                issues.append(
                    f"Technical debt {technical_debt}% above threshold {self.config['sonarqube']['max_technical_debt']}%"
                )

            result = {
                "status": "PASSED" if passed else "FAILED",
                "quality_score": quality_score,
                "coverage": coverage,
                "duplications": duplications,
                "technical_debt": technical_debt,
                "issues": issues,
            }

            logger.info(f"SonarQube check: {result['status']}")
            return result

        except Exception as e:
            logger.error(f"Error checking SonarQube: {e}")
            return {"status": "ERROR", "error": str(e)}

    def check_semgrep_security(self) -> Dict:
        """Check Semgrep security scan results"""
        logger.info("Checking Semgrep security scan...")

        try:
            # Check if Semgrep results exist
            semgrep_results = Path("semgrep-results.json")
            if not semgrep_results.exists():
                logger.warning("Semgrep results not found, skipping check")
                return {"status": "SKIPPED", "reason": "Results not found"}

            # Parse Semgrep results
            with open(semgrep_results, "r") as f:
                data = json.load(f)

            # Count issues by severity
            critical_issues = []
            high_issues = []
            medium_issues = []

            for result in data.get("results", []):
                severity = result.get("extra", {}).get("severity", "UNKNOWN")
                if severity == "ERROR":
                    critical_issues.append(result)
                elif severity == "WARNING":
                    high_issues.append(result)
                elif severity == "INFO":
                    medium_issues.append(result)

            # Check thresholds
            passed = True
            issues = []

            if len(critical_issues) > self.config["semgrep"]["max_critical"]:
                passed = False
                issues.append(
                    f"Critical issues {len(critical_issues)} above threshold {self.config['semgrep']['max_critical']}"
                )

            if len(high_issues) > self.config["semgrep"]["max_high"]:
                passed = False
                issues.append(
                    f"High issues {len(high_issues)} above threshold {self.config['semgrep']['max_high']}"
                )

            if len(medium_issues) > self.config["semgrep"]["max_medium"]:
                passed = False
                issues.append(
                    f"Medium issues {len(medium_issues)} above threshold {self.config['semgrep']['max_medium']}"
                )

            result = {
                "status": "PASSED" if passed else "FAILED",
                "critical_issues": len(critical_issues),
                "high_issues": len(high_issues),
                "medium_issues": len(medium_issues),
                "total_issues": len(critical_issues)
                + len(high_issues)
                + len(medium_issues),
                "issues": issues,
            }

            logger.info(f"Semgrep check: {result['status']}")
            return result

        except Exception as e:
            logger.error(f"Error checking Semgrep: {e}")
            return {"status": "ERROR", "error": str(e)}

    def check_bandit_security(self) -> Dict:
        """Check Bandit security scan results"""
        logger.info("Checking Bandit security scan...")

        try:
            # Check if Bandit results exist
            bandit_results = Path("bandit-results.json")
            if not bandit_results.exists():
                logger.warning("Bandit results not found, skipping check")
                return {"status": "SKIPPED", "reason": "Results not found"}

            # Parse Bandit results
            with open(bandit_results, "r") as f:
                data = json.load(f)

            # Count issues by severity
            high_issues = []
            medium_issues = []
            low_issues = []

            for result in data:
                severity = result.get("issue_severity", "UNKNOWN")
                confidence = result.get("issue_confidence", 0)

                if severity == "HIGH":
                    high_issues.append(result)
                elif severity == "MEDIUM":
                    medium_issues.append(result)
                elif severity == "LOW":
                    low_issues.append(result)

            # Check thresholds
            passed = True
            issues = []

            if len(high_issues) > self.config["bandit"]["max_high"]:
                passed = False
                issues.append(
                    f"High issues {len(high_issues)} above threshold {self.config['bandit']['max_high']}"
                )

            if len(medium_issues) > self.config["bandit"]["max_medium"]:
                passed = False
                issues.append(
                    f"Medium issues {len(medium_issues)} above threshold {self.config['bandit']['max_medium']}"
                )

            # Check confidence levels
            low_confidence_issues = [
                r
                for r in data
                if r.get("issue_confidence", 0)
                < self.config["bandit"]["min_confidence"]
            ]
            if low_confidence_issues:
                logger.warning(
                    f"Found {len(low_confidence_issues)} low confidence issues"
                )

            result = {
                "status": "PASSED" if passed else "FAILED",
                "high_issues": len(high_issues),
                "medium_issues": len(medium_issues),
                "low_issues": len(low_issues),
                "total_issues": len(high_issues) + len(medium_issues) + len(low_issues),
                "low_confidence_issues": len(low_confidence_issues),
                "issues": issues,
            }

            logger.info(f"Bandit check: {result['status']}")
            return result

        except Exception as e:
            logger.error(f"Error checking Bandit: {e}")
            return {"status": "ERROR", "error": str(e)}

    def check_owasp_zap_security(self) -> Dict:
        """Check OWASP ZAP security scan results"""
        logger.info("Checking OWASP ZAP security scan...")

        try:
            # Check if OWASP ZAP results exist
            zap_results = Path("zap-results.json")
            if not zap_results.exists():
                logger.warning("OWASP ZAP results not found, skipping check")
                return {"status": "SKIPPED", "reason": "Results not found"}

            # Parse OWASP ZAP results
            with open(zap_results, "r") as f:
                data = json.load(f)

            # Extract security metrics
            security_score = data.get("securityScore", 0)
            critical_vulns = len(data.get("critical", []))
            high_vulns = len(data.get("high", []))
            medium_vulns = len(data.get("medium", []))
            low_vulns = len(data.get("low", []))

            # Check thresholds
            passed = True
            issues = []

            if security_score < self.config["owasp_zap"]["min_security_score"]:
                passed = False
                issues.append(
                    f"Security score {security_score} below threshold {self.config['owasp_zap']['min_security_score']}"
                )

            if critical_vulns > self.config["owasp_zap"]["max_critical"]:
                passed = False
                issues.append(
                    f"Critical vulnerabilities {critical_vulns} above threshold {self.config['owasp_zap']['max_critical']}"
                )

            if high_vulns > self.config["owasp_zap"]["max_high"]:
                passed = False
                issues.append(
                    f"High vulnerabilities {high_vulns} above threshold {self.config['owasp_zap']['max_high']}"
                )

            result = {
                "status": "PASSED" if passed else "FAILED",
                "security_score": security_score,
                "critical_vulns": critical_vulns,
                "high_vulns": high_vulns,
                "medium_vulns": medium_vulns,
                "low_vulns": low_vulns,
                "total_vulns": critical_vulns + high_vulns + medium_vulns + low_vulns,
                "issues": issues,
            }

            logger.info(f"OWASP ZAP check: {result['status']}")
            return result

        except Exception as e:
            logger.error(f"Error checking OWASP ZAP: {e}")
            return {"status": "ERROR", "error": str(e)}

    def run_all_checks(self) -> Dict:
        """Run all quality gate checks"""
        logger.info("Running all quality gate checks...")

        # Run individual checks
        self.results["gates"]["sonarqube"] = self.check_sonarqube_quality_gate()
        self.results["gates"]["semgrep"] = self.check_semgrep_security()
        self.results["gates"]["bandit"] = self.check_bandit_security()
        self.results["gates"]["owasp_zap"] = self.check_owasp_zap_security()

        # Determine overall status
        all_passed = True
        skipped_count = 0
        error_count = 0

        for gate_name, gate_result in self.results["gates"].items():
            if gate_result["status"] == "FAILED":
                all_passed = False
            elif gate_result["status"] == "SKIPPED":
                skipped_count += 1
            elif gate_result["status"] == "ERROR":
                error_count += 1
                all_passed = False

        # Set overall status
        if all_passed:
            if skipped_count == len(self.results["gates"]):
                self.results["overall_status"] = "SKIPPED"
            else:
                self.results["overall_status"] = "PASSED"
        else:
            self.results["overall_status"] = "FAILED"

        # Generate summary
        self.results["summary"] = {
            "total_gates": len(self.results["gates"]),
            "passed_gates": sum(
                1 for r in self.results["gates"].values() if r["status"] == "PASSED"
            ),
            "failed_gates": sum(
                1 for r in self.results["gates"].values() if r["status"] == "FAILED"
            ),
            "skipped_gates": skipped_count,
            "error_gates": error_count,
        }

        logger.info(f"Overall quality gate status: {self.results['overall_status']}")
        return self.results

    def save_results(self, output_path: str = "quality_gate_results.json"):
        """Save quality gate results to file"""
        try:
            with open(output_path, "w") as f:
                json.dump(self.results, f, indent=2, default=str)
            logger.info(f"Results saved to {output_path}")
        except Exception as e:
            logger.error(f"Error saving results: {e}")

    def print_summary(self):
        """Print quality gate summary"""
        print("\n" + "=" * 60)
        print("SPECULA QUALITY GATE CHECK RESULTS")
        print("=" * 60)
        print(f"Timestamp: {self.results['timestamp']}")
        print(f"Overall Status: {self.results['overall_status']}")
        print()

        print("Gate Results:")
        print("-" * 40)
        for gate_name, gate_result in self.results["gates"].items():
            status_icon = (
                "✅"
                if gate_result["status"] == "PASSED"
                else "❌" if gate_result["status"] == "FAILED" else "⚠️"
            )
            print(f"{status_icon} {gate_name.upper()}: {gate_result['status']}")

            if gate_result["status"] == "FAILED" and "issues" in gate_result:
                for issue in gate_result["issues"]:
                    print(f"    • {issue}")

        print()
        print("Summary:")
        print("-" * 40)
        summary = self.results["summary"]
        print(f"Total Gates: {summary['total_gates']}")
        print(f"Passed: {summary['passed_gates']}")
        print(f"Failed: {summary['failed_gates']}")
        print(f"Skipped: {summary['skipped_gates']}")
        print(f"Errors: {summary['error_gates']}")

        print()
        if self.results["overall_status"] == "PASSED":
            print("🎉 All quality gates passed!")
        elif self.results["overall_status"] == "FAILED":
            print("❌ Quality gates failed!")
        else:
            print("⚠️ Quality gates skipped or had errors")

        print("=" * 60)


def main():
    """Main entry point"""
    try:
        # Initialize checker
        checker = QualityGateChecker()

        # Run all checks
        results = checker.run_all_checks()

        # Save results
        checker.save_results()

        # Print summary
        checker.print_summary()

        # Exit with appropriate code
        if results["overall_status"] == "PASSED":
            sys.exit(0)
        else:
            sys.exit(1)

    except Exception as e:
        logger.error(f"Fatal error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
